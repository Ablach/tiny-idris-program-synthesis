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
 lhs : RawImp
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
                  List RawImp -> Core (List (Term [], Glued [], RawImp))
filterCheckable [] = pure []
filterCheckable (x :: xs) =
  do newRef EFail False
     (tm, gd) <- catch (checkTerm [] x Nothing) 
                       (\ _ => do put EFail True
                                  pure (Erased, MkGlue (pure Erased)
                                                       (\_ => pure NErased)))
     if !(get EFail)
        then filterCheckable xs
        else pure ((tm, gd, x) :: !(filterCheckable xs))



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
                Term ns -> Env Term ns -> RawImp ->
                (vars ** (Env Term vars, Term vars, RawImp))
getSearchData (Bind x (PVTy y) scope) env ri
  = getSearchData scope (PVar x y :: env) ri
getSearchData tm env ri = (ns ** (env , tm, ri))

getClause : {vars : _} -> 
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            (Search vars , Term vars, RawImp) -> 
            -- search contains the env and the overall type, 
            -- the term is the rhs
            -- we can't use get args here since we may have altered
            -- then environmente
            Core (Clause, RawImp, RawImp)
getClause ((MkSearch depth name env lhs target), rt, lt) 
  = do let tm = getLhs lt
       (ctm , gd) <- checkTerm env tm Nothing 
       pure ((MkClause env ctm rt), lt, (unelab rt))
 where
  getLhs : RawImp -> RawImp
  getLhs (IPatvar m t scope)
    = getLhs scope
  getLhs tm = tm



tryIfSuccessful : {vars :_} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  (Search vars) ->
                  Name -> NameType ->
                  NF vars -> Core (List (Term vars))
tryIfSuccessful s@(MkSearch (S depth) name env lhs target) n nty (NBind m (Pi nm pinfo tm) sc)
  = do defs <- get Ctxt
       (tm' :: ts) <- synthesise (MkSearch (pred depth) m env lhs !(quote defs env tm))
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
tryIfSuccessful (MkSearch 0 name env lhs target) n nty tm = none
tryIfSuccessful (MkSearch depth name env lhs target) n nty tm 
  = do defs <- get Ctxt
       --log $ "trying " ++ (show target) ++ " and " ++ (show !(quote defs env tm))
       Just (MkUnifyResult [] holesSolved) <- tryUnify env target !(quote defs env tm)
        | _ => none 
 --      if holesSolved then log $ "holes solved" else log "no holes solved"
       --showCons constraints
       pure [Ref nty n]

structuralRecursionCheck : {vars : _} -> {vars' :_} ->
                           {auto c : Ref Ctxt Defs} ->
                           {auto u : Ref UST UState} ->
                           Term vars -> Term vars' ->
                           Core Bool
structuralRecursionCheck (Bind x y scope) (Bind x' y' scope') 
  = structuralRecursionCheck scope scope'
structuralRecursionCheck tm tm'
  = do log $ "running on " ++ (show tm) ++ " and " ++ (show tm')
       let (f, as) = getFnArgs tm
           (f', as') = getFnArgs tm'
       pure $ feq f f' && !(aeq as as')
  where
    feq : Term vars -> Term vars' -> Bool
    feq (Ref x y) (Ref z w) = not (w == y)
    feq _ _ = True
    
    aeq : List (Term vars) -> List (Term vars') -> Core Bool
    aeq (x :: xs) (y :: ys) = if !(structuralRecursionCheck x y) 
                                 then pure True 
                                 else aeq xs ys
    aeq [] [] = pure False
    aeq _ _ = pure True


sr : {vars: _} -> {auto c : Ref Ctxt Defs} ->  RawImp -> Term vars -> Core Bool 
sr lhs tm = sr' lhs (unelab tm)
  where sr' : RawImp -> RawImp -> Core Bool 
        sr' (IPatvar a b x) tm = sr' x tm
        sr' (IApp f x) (IApp f' y) 
          = do log $ "here with " ++ (resugar (IApp f x)) ++ " and " ++ (resugar (IApp f' y))
               if !(sr' x y) then pure True else sr' f f'
        sr' (IVar x) (IVar y) 
        = do log $ (show x) ++ " and " ++ (show y) ++ " returning " ++ (show (not (x ==y)))
             pure $ not (x == y)
        sr' _ _ = pure True

tryDef : {vars : _} ->
         {auto c : Ref Ctxt Defs} -> 
         {auto u : Ref UST UState} ->
         Search vars -> Name -> NameType ->
         Term [] -> Core (List (Term vars))
tryDef s@(MkSearch depth name env lhs target) n nty tm 
 = do defs <- get Ctxt
      norm <- nf defs env (rewrite sym (appendNilRightNeutral vars) in weakenNs vars tm)
      (ntm , args) <- fillMetas env norm
      deleteMetas args
      qtm <- quote defs env ntm
      Just cs <- tryUnify env target qtm
        | _ => none
      (can :: candidates) <- tryIfSuccessful s n nty norm | _ => none
      if n == (UN "Cons")
       then do log $ show can
               log $ resugar $ unelab can
               log $ resugar lhs 
               log $ resugar (ge lhs)
       else pure ()
      if n == name 
       then do log $ show can
               log $ resugar $ unelab can
               log $ resugar lhs 
               log $ resugar (ge lhs)
               filterM (sr lhs) candidates
       else pure (can :: candidates)
  where ge : RawImp -> RawImp
        ge (IPatvar x ty scope) = ge scope 
        ge tm = tm 


tryLocals : {vars : _} -> 
            {auto c : Ref Ctxt Defs} -> 
            {auto u : Ref UST UState} ->
            Search vars -> 
            (usable : List (Term vars)) ->
            Core (List (Term vars))
tryLocals s@(MkSearch depth name env lhs target) (l@(Local idx p) :: usable)
 = case !(tryUnify env target (binderType $ getBinder p env)) of 
        Just (MkUnifyResult [] holesSolved) => 
           do --  log $ "found " ++ (resugar $ unelab env (Local idx p)) ++ " for " ++ (show target)
              pure (Local idx p :: !(tryLocals s usable))
        _ => tryLocals s usable
tryLocals _ _ = none



synthesise (MkSearch depth name env lhs (Bind n (Pi n' pinfo tm) scope)) 
 = pure $ map (Bind n (Lam n' pinfo tm))
              !(synthesise (MkSearch depth n (Lam n' pinfo tm :: env) lhs scope))
synthesise s@(MkSearch d name env lhs TType) 
  = pure $ !(tryLocals s (getUsableEnv [] env)) ++ !typeRefs
synthesise s@(MkSearch 0 name env lhs tm)
 = tryLocals s (getUsableEnv [] env)
synthesise s@(MkSearch (S k) name env lhs tm)
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

synthesiseWorlds : {auto c : Ref Ctxt Defs} -> 
                   {auto u : Ref UST UState} -> 
                   Name ->
                   List (vars ** (Env Term vars , Term vars, RawImp)) ->
                   Core (Maybe (List (Clause, RawImp, RawImp)))
synthesiseWorlds n [] = pure $ Just []
synthesiseWorlds n ((vars ** (env, tm, ri)) :: xs)
 = do let s = (MkSearch 4 n env ri tm)
      (t :: ts) <- synthesise s | _ => nothing 
      Just rest <- synthesiseWorlds n xs | _ => nothing
      clause <- getClause (s, t, ri)
      pure $ Just (clause :: rest)

showclauses : {auto c : Ref Ctxt Defs} -> 
              {auto u : Ref UST UState} -> 
              List Clause -> Core () 
showclauses [] = pure ()
showclauses ((MkClause env lhs rhs) :: xs) 
 = do log $ "lhs " ++ (resugar $ unelab lhs) ++ " rhs " ++ (resugar $ unelab rhs)
      showclauses xs

synthesisePM : {auto c : Ref Ctxt Defs} -> 
               {auto u : Ref UST UState} ->
               Name -> Term []->
               List (vars ** (Env Term vars , Term vars, RawImp)) ->
               Core (Maybe (Def, List (Clause, RawImp, RawImp)))
synthesisePM n ty ss
  = do Just clauses <- synthesiseWorlds n ss | _ => nothing
--       showclauses clauses
       (as ** ct) <- getPMDef n ty $ map (\ (a,_,_) => a) clauses
       pure $ Just (PMDef as ct, clauses)


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
        Core (Maybe (Def, List (Clause, RawImp, RawImp)))
begin def n lhs = 
  do cs@(c :: cases) <- traverse splitLhs lhs | _ => pure Nothing
     let cs' = concat cs
     gs@(p :: ps) <- filterCheckable cs' | _ => pure Nothing
     Just res <- synthesisePM n (type def)
                  !(traverse (\(tm , gty, ri) => pure $ getSearchData !(getTerm gty) [] ri) gs)
      | _ => begin def n cs'
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
                    Just (res, clauses) => pure $ resugarType clauses n $ unelab (type def)
                    Nothing  => pure "No match"
               (MetaVar vars env retTy) => 
                do let Just lhs = lookup n (userholes ust) | _ => pure "Missing hole"
                   (r :: rs) <- synthesise (MkSearch 4 n env lhs retTy)                        
                    | _ => pure "No match"
                   -- here we want to add in some heuristic for sorting
                   pure $ resugar $ unelab r
               _ => pure "Invalid definition"



