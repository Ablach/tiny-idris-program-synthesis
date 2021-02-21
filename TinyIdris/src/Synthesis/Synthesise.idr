module Synthesis.Synthesise

import Core.CaseBuilder
import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Unify
import Core.UnifyState
import Core.Value

import TTImp.Elab.Term
import TTImp.TTImp

import Synthesis.Rescope
import Synthesis.Unelab
import Synthesis.Resugar
import Synthesis.Util

import Data.List
import Data.Nat
import Data.Maybe
import Data.Either
import Data.SortedMap

-- Exists purely to clean up type signatures
record Search (vars : List Name) where
 constructor MkSearch
 depth : Nat
 name : Name
 env : Env Term vars
 target : Term vars 

synthesise : {vars : _} -> 
             {auto c : Ref Ctxt Defs} -> 
             {auto u : Ref UST UState} ->
             Search vars -> Core (List (Term vars))


data UFail : Type where
data EFail : Type where
export
tryUnify : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           Env Term vars ->
           Term vars -> Term vars -> 
           Core (Maybe (UnifyResult))
tryUnify env a b
  = do 
       newRef UFail False 
       ures <- catch (unify env a b) 
                     (\_ => do put UFail True 
                               pure $ MkUnifyResult [] False)
       if !(get UFail) 
          then nothing 
          else pure $ Just (ures)

filterCheckable : {auto c : Ref Ctxt Defs} -> 
                  {auto u : Ref UST UState} ->
                  List RawImp -> Core (List (Term [], Glued []))
filterCheckable [] = pure []
filterCheckable (x :: xs) =
  do newRef EFail False
     g <- catch (checkTerm [] x Nothing) 
                (\ _ => do put EFail True
                           pure (Erased, MkGlue (pure Erased) (\_ => pure NErased)))
     if !(get EFail)
        then filterCheckable xs
        else pure (g :: !(filterCheckable xs))



fillMetas : {vars : _} -> 
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Env Term vars -> NF vars ->
            Core (NF vars , List (Term vars, Name))
fillMetas env (NBind n (Pi n' pinfo tm) scope) 
  = do defs <- get Ctxt 
       nm <- genName "filling"
       mta <- newMeta env nm !(quote defs env tm) Hole
       (f , args) <- fillMetas env !(scope defs (toClosure env mta))
       pure (f , (mta , nm) :: args)
fillMetas env tm = pure (tm , [])


getSearchData : {ns : _} -> 
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                Term ns -> Env Term ns ->
                (vars ** (Env Term vars, Term vars))
getSearchData (Bind x (PVTy y) scope) env
  = getSearchData scope (PVar x y :: env)
getSearchData tm env = (ns ** (env , tm))



getClause' : {vars : _} ->
             Env Term vars -> Name -> 
             Term vars
getClause' [] n = Ref Func n
getClause' ((Pi x y z) :: xs) n = weaken $ App (getClause' xs n) z
getClause' ((PVar x y) :: xs) n = weaken $ App (getClause' xs n) y
getClause' (_ :: xs) n = weaken $ getClause' xs n

getClause : {vars : _} -> 
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            (Search vars , Term vars) -> 
            -- search contains the env and the overall type, 
            -- the term is the rhs
            -- we can't use get args here since we may have altered
            -- then environmente
            Core Clause
getClause ((MkSearch depth name env target), rt) 
  = pure $ MkClause env (getClause' env name) rt

showC : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} -> 
        List Int -> Core ()
showC [] = pure ()
showC (x :: xs) = do ust <- get UST
                     let (Just c) = lookup x (constraints ust)
                      | _ => log "constraint not found"
                     case c of 
                      (MkConstraint env y z) => log $ (show y) ++ " = " ++ (show z)
                      (MkSeqConstraint env ys zs) => log $ "seq"
                      Resolved => log "resolved"
                     

getRef : {vars :_} -> 
         {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         Env Term vars -> Term vars -> Name -> Core (Term vars)
getRef env tm n 
  = do defs <- get Ctxt
       Just def <- lookupDef n defs
        | _ => ?nah 
       let (fn,as) = getFnArgs (type def)
       log $ show $ map show as
       case definition def of 
         (DCon tag arity) =>
            do (m , ms) <- fillMetas env 
                                     !(nf defs env $
                                         rewrite sym (appendNilRightNeutral vars) 
                                              in weakenNs vars (type def))
               Just res <- tryUnify env !(quote defs env m) tm
                | _ => pure $ apply (Ref (DataCon tag arity) n) !(traverse (\ (a,b) => quote defs env a) ms)
               pure $ apply (Ref (DataCon tag arity) n) !(traverse (\ (a,b) => quote defs env a) ms)
         _ => ?nah2                

{-
getRef : {vars :_} -> 
         {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         Env Term vars -> Term vars -> Name -> Core (Term vars)
getRef env tm n 
  = do let (fn, as) = getFnArgs tm
       log $ show $ map show as
       pure TType
       -}
replaceTop : {n : _} -> {vars : _} ->
             Env Term (x :: vars) ->
             Term vars ->
             Env Term (x :: vars) 
replaceTop ((Lam y w v) :: z) tm = ((Lam y w tm) :: z)  
replaceTop ((Pi y w v) :: z) tm = ((Pi y w tm) :: z)  
replaceTop ((PVar y w) :: z) tm = ((PVar y tm) :: z)  
replaceTop ((PVTy y) :: z) tm = ((PVTy y) :: z)


splitEnv : {vars : _} -> 
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Env Term vars -> 
           Core (Either (Env Term vars) (List (Env Term vars)))
splitEnv [] = pure $ Left []
splitEnv {vars = (x :: vars')} e@((PVar n (Meta m ns)) :: env') 
 = do defs <- get Ctxt
      Left ere <- splitEnv env'
        | _ => ?fdsds
      Just d <- lookupDef m defs
        | _ => do log "splitenv not in context" ; pure $ Left e
      log $ show $ type d
      log $ show m
      log $ resugarDef (definition d)      
      pure $ Left e
splitEnv {vars = (x :: vars')} e@((PVar n tm) :: env') 
 = do defs <- get Ctxt
      Left env'' <- splitEnv env' 
       | Right env'' => do res <- traverse (\ en => do tm' <- normalise defs en tm
                                                       pure $ ((PVar n tm') :: en)) env'' 
                           pure $ Right res
      let (Ref (TyCon tag arity) n', as) = getFnArgs tm
       | _ => pure $ Left e 
      Just ty <- lookupDef n' defs
       | _ => ?shouldnt_happen
      let (TCon tag' arity' datas) = definition ty
       | _ => ?impossible2
      ts <- traverse (getRef {vars = vars'} env' tm) datas
      pure $ Right $ map (replaceTop {n = x} {vars = vars'} e) ts
splitEnv (bdr :: env) = case !(splitEnv env) of 
                        (Left x) => pure $ Left $ (bdr :: x)
                        (Right x) => pure $ Right $ map (bdr ::) x


--pure $ Right $ map (\ en => (PVar n !(normalise defs en tm)) :: en) env'' 
tryIfSuccessful : {vars :_} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  (Search vars) ->
                  Name -> NameType ->
                  NF vars -> Core (List (Term vars))
tryIfSuccessful s@(MkSearch (S depth) name env target) n nty (NBind m (Pi nm pinfo tm) sc)
  = do defs <- get Ctxt
       (tm' :: ts) <- synthesise (MkSearch (pred depth) m env !(quote defs env tm))
        | _ => none
       results <- traverse help (tm' :: ts)
       pure $ concat results
  where help : Term vars ->
               Core (List (Term vars))
        help tm
         = do defs <- get Ctxt
              sc' <- sc defs (toClosure env tm)
              (filled , fas) <- fillMetas env sc'
              Just ures <- tryUnify env target !(quote defs env filled)
               | _ => do deleteMetas fas ;  none
              deleteMetas fas
              
              --log $ "trying " ++ (show tm) ++ "with scope " ++ (show !(quote defs env sc'))
              (r :: rs) <- tryIfSuccessful s n nty sc'
               | _ => none
              pure $ map (\ z => App z tm) (r :: rs)
tryIfSuccessful (MkSearch 0 name env target) n nty tm = none
tryIfSuccessful (MkSearch depth name env target) n nty tm 
  = do defs <- get Ctxt
       --log $ "trying " ++ (show target) ++ " and " ++ (show !(quote defs env tm))
       Just (MkUnifyResult [] holesSolved) <- tryUnify env target !(quote defs env tm)
        | _ => none 
 --      if holesSolved then log $ "holes solved" else log "no holes solved"
       --showCons constraints
       pure [Ref nty n]


tryDef : {vars : _} ->
         {auto c : Ref Ctxt Defs} -> 
         {auto u : Ref UST UState} ->
         Search vars -> Name -> NameType ->
         Term [] -> Core (List (Term vars))
tryDef s@(MkSearch depth name env target) n nty tm 
 = do defs <- get Ctxt
      norm <- nf defs env (rewrite sym (appendNilRightNeutral vars) in weakenNs vars tm)
      (ntm , args) <- fillMetas env norm
      deleteMetas args
      qtm <- quote defs env ntm
      Just cs <- tryUnify env target qtm
        | _ => none
      tryIfSuccessful s n nty norm 
      

tryLocals : {vars : _} -> 
            {auto c : Ref Ctxt Defs} -> 
            {auto u : Ref UST UState} ->
            Search vars -> 
            (usable : List (Term vars)) ->
            Core (List (Term vars))
tryLocals s@(MkSearch depth name env target) (l@(Local idx p) :: usable)
 = case !(tryUnify env target (binderType $ getBinder p env)) of 
        Just (MkUnifyResult [] holesSolved) => 
           do --  log $ "found " ++ (resugar $ unelab env (Local idx p)) ++ " for " ++ (show target)
              pure (Local idx p :: !(tryLocals s usable))
        _ => tryLocals s usable
tryLocals _ _ = none



synthesise (MkSearch depth name env (Bind n (Pi n' pinfo tm) scope)) 
 = pure $ map (Bind n (Lam n' pinfo tm))
              !(synthesise (MkSearch depth n (Lam n' pinfo tm :: env) scope))
synthesise s@(MkSearch d name env TType) 
  = pure $ !(tryLocals s (getUsableEnv [] env)) ++ !typeRefs
synthesise s@(MkSearch 0 name env tm)
 = tryLocals s (getUsableEnv [] env)
synthesise s@(MkSearch (S k) name env tm)
 = do defs <- get Ctxt
      ust <- get UST
      locals <- tryLocals s (getUsableEnv [] env)
      cons <- case getFnArgs tm of 
                ((Ref nty@(TyCon tag arity) n), as)
                   => do Just def <- lookupDef n defs
                          | _ => none
                         let (TCon tag' arity' datacons) = definition def
                          | _ => none
                         pure $ concat  !(traverse (\ x => 
                                             do Just d <- lookupDef x defs | _ => none
                                                let (DCon t a) = definition d | _ => none
                                                tryDef s x (DataCon t a) (type d)) datacons) 
                _ => none
      let funcs : List (Name , Term []) = toList $ functions ust
      let fs = concat $ !(traverse (\ (fn, ft) => tryDef s fn Func ft) $ funcs)
      pure (locals ++ cons ++ fs)

showCns : {auto c : Ref Ctxt Defs} -> Term vars -> Core String
showCns (Local idx p) = pure "local"
showCns (Ref x y) = pure "ref "
showCns (Meta x xs) = do defs <- get Ctxt
                         Just d <- lookupDef x defs  
                          | _ => ?dasdad
                         case definition d of
                              None => log "none"
                              (PMDef args treeCT) => log "pm"
                              (DCon tag arity) => log "dcon"
                              (TCon tag arity datacons) => log "tcon"
                              Hole => log "hole"
                              (MetaVar ys y retTy) => log "meta"
                              (Guess guess constraints) => log "guess"
                         log $ show (type d)
                         pure $ "meta " ++ (show x) 
showCns (Bind x y scope) = pure "bind"
showCns (App x y) = pure $ "app " ++ !(showCns y)
showCns TType = pure "tty"
showCns Erased = pure "erased"

showT : Term vars -> String
showT (Local idx p) = "local"
showT (Ref x y) = "ref"
showT (Meta x xs) = "meta"
showT (Bind x y scope) = "bind"
showT (App x y) = "app"
showT TType = "tty"
showT Erased = "erased"

showE : {vars :_} -> {auto c : Ref Ctxt Defs} -> Env Term vars -> Core String
showE [] = pure "empty"
showE ((Lam x z w) :: y) 
  = pure $ "lam " ++ (show x) ++ " " ++ (showT w) ++ " " ++ 
    (show !(normalise !(get Ctxt) y w)) ++ ",\n " ++ !(showE y)
showE ((Pi x z w) :: y) 
  = pure $ "pi " ++ (show x) ++ " " ++ (showT w) ++ " " ++ 
    (show !(normalise !(get Ctxt) y w)) ++ ",\n " ++ !(showE y) 
showE ((PVar x z) :: y)
  = pure $ "pvar " ++ (show x) ++ " " ++ (showT z) ++ " " ++
    (show !(normalise !(get Ctxt) y z))++ ",\n " ++ !(showE y) 
showE ((PVTy x) :: y) 
  = pure $ "pvty " ++ (showT x) ++ " " ++ (show x) ++ "\n" ++ !(showE y)


showS : {vars :_} -> {auto c : Ref Ctxt Defs} -> Search vars -> Core ()
showS (MkSearch depth name env target) 
  = log $ "Search: depth = " ++ (show depth) ++
          " name = " ++ (show name) ++ 
          " env =\n " ++ !(showE env) ++
          "\ntarget = " ++ (show target)


normE : {vars : _} -> 
        {auto c : Ref Ctxt Defs} -> 
        {auto u : Ref UST UState} -> 
        Env Term vars -> Core (Env Term vars)
normE [] = pure []
normE ((PVar x z) :: y) 
  = do defs <- get Ctxt
       tm <- normalise defs y z
       pure (PVar x tm :: !(normE y))
normE (tm :: y) = pure (tm :: !(normE y))

synthesiseWorlds : {auto c : Ref Ctxt Defs} -> 
                   {auto u : Ref UST UState} -> 
                   Name ->
                   List (vars ** (Env Term vars , Term vars)) ->
                   Core (Maybe (List Clause))
synthesiseWorlds n [] = pure $ Just []
synthesiseWorlds n ((vars ** (env, tm)) :: xs)
 = do let s = (MkSearch 3 n env tm)
      showS s     
      (t :: ts) <- synthesise s | _ => nothing
      traverse (log . show) (t :: ts)
      Just rest <- synthesiseWorlds n xs | _ => nothing
      clause <- getClause (s, t)
      pure $ Just (clause :: rest)


synthesisePM : {auto c : Ref Ctxt Defs} -> 
               {auto u : Ref UST UState} ->
               Name -> Term []->
               List (vars ** (Env Term vars , Term vars)) ->
               Core (Maybe Def)
synthesisePM n ty ss 
  = do Just clauses <- synthesiseWorlds n ss | _ => nothing
       (as ** ct) <- getPMDef n ty clauses
       pure $ Just (PMDef as ct)


splitLhs : {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           RawImp -> Core (List RawImp)
splitLhs (IPatvar x ty scope) 
  = do defs <- get Ctxt
       let (IVar n) = getFn ty | _ => cont
       Just def <- lookupDef n defs | _ => cont
       let (TCon tag arity datas) = definition def | _ => cont
       pats <- traverse getConPatterns datas
       let finals = map (\ (fs, sn) => ((fixUpScope x scope fs) , sn)) pats
       pure $ merge finals
       -- for each data constructor,  remove the pattern for n, and add patterns for their 
       -- args, then a : _ ect, then apply f (constructor a..an) args...
   where 
         merge : List (a , a -> b) -> List b
         merge = map (\ (fs, sn) => sn fs) 

         fixUpScope : Name ->
                      (scope : RawImp) ->
                      (replacement : RawImp) ->
                      RawImp
         fixUpScope n (IVar x) rep 
          = if x == n then rep else (IVar x)
         fixUpScope n (IApp f tm) rep 
          = IApp (fixUpScope n f rep) (fixUpScope n tm rep)
         fixUpScope n (IPi y z argTy retTy) rep 
          = IPi y z (fixUpScope n argTy rep) (fixUpScope n retTy rep)
         fixUpScope n (ILam y z argTy w) rep 
          = ILam y z (fixUpScope n argTy rep) (fixUpScope n w rep)
         fixUpScope n (IPatvar y z w) rep 
          = IPatvar y (fixUpScope n z rep) (fixUpScope n w rep) 
         fixUpScope n tm rep = tm

         genNames : Nat -> Core (List Name)
         genNames Z = none
         genNames (S k) = do nm <- genName $ "x" ++ (show (S k))
                             ns <- genNames k
                             pure (nm :: ns)

         toPatVar : List Name -> RawImp -> RawImp
         toPatVar [] ri = ri
         toPatVar (n :: ns) ri = IPatvar n Implicit (toPatVar ns ri)

         getConPatterns : Name -> Core (RawImp, (RawImp -> RawImp))
         getConPatterns n
            = do defs <- get Ctxt
                 Just def <- lookupDef n defs | _ => ?sdf
                 let (DCon t a) = definition def | _ => ?sdf1
                 ns <- genNames a
                 let ns' = map IVar ns
                 pure $ (apply (IVar n) ns' , toPatVar ns)

         cont : Core (List RawImp) 
         cont = do (r :: rs) <- splitLhs scope | _ => none
                   pure $ map (IPatvar x ty) (r :: rs)
splitLhs _ = none

getLhs : {vars :_} -> {auto c : Ref Ctxt Defs} -> Term vars -> Name -> List RawImp -> RawImp 
getLhs (Bind x (Pi m pinfo tm) scope) n ls 
  = let tm' = unelab tm
        sc = getLhs scope n ((IVar m) :: ls) in
         IPatvar x tm' sc
getLhs tm n ls = apply (IVar n) (reverse ls)


begin : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} -> 
        GlobalDef -> Name -> List RawImp -> 
        Core (Maybe Def)
begin def n lhss = 
  do (c :: cases) <- traverse splitLhs lhss | _ => pure Nothing
     let cs = concat (c :: cases) 
     gs@(p :: ps) <- filterCheckable cs | _ => pure Nothing
     Just res <- synthesisePM n (type def)
                  !(traverse (\(tm , gty) => pure $ getSearchData !(getTerm gty) []) gs)
      | _ => begin def n cs
     pure $ Just res

public export
run : {auto c : Ref Ctxt Defs} -> 
      {auto u : Ref UST UState} ->
      Name -> Core String
run n = do Just def <- lookupDef n !(get Ctxt)
            | _ => pure "Invalid Name" 
           ust <- get UST
           case definition def of
               None =>
                  case !(begin def n [getLhs (type def) n []]) of
                    Just res => pure $ resugarDef res
                    Nothing  => pure "No match"
               (MetaVar vars env retTy) => 
                do (r :: rs) <- synthesise (MkSearch 4 n env retTy)                        
                    | _ => pure "No match"
                   -- here we want to add in some heuristic for sorting
                   pure $ resugar $ unelab r
               _ => pure "Invalid definition"



