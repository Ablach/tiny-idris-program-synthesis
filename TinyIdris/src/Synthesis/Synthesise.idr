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
import Synthesis.CaseSplit
import Synthesis.Order
import Synthesis.Search

import Data.List
import Data.Nat
import Data.Maybe
import Data.Either
import Data.SortedMap

synthesise : {vars : _} -> 
             {auto c : Ref Ctxt Defs} -> 
             {auto u : Ref UST UState} ->
             Search vars -> Core (List (Term vars))



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
       pure $ concat !(traverse help (tm' :: ts))
       
  where pushdown : Term vars -> Term vars -> Term vars
        pushdown tm (Ref nty n) = App (Ref nty n) tm
        pushdown tm (App f a) = App (pushdown tm f) a
        pushdown tm f = App f tm
      
        help : Term vars ->
               Core (List (Term vars))
        help tm
         = do defs <- get Ctxt
              sc' <- sc defs (toClosure env tm)
              (filled , fas) <- fillMetas env sc'
              Just ures <- tryUnify env target !(quote defs env filled)
               | _ => none
              (r :: rs) <- tryIfSuccessful s n nty sc'
               | _ => none
              pure $ map (pushdown tm) (r :: rs)    
tryIfSuccessful (MkSearch 0 name env lhs target) n nty tm = none 
tryIfSuccessful (MkSearch depth name env lhs target) n nty tm 
  = do defs <- get Ctxt
       Just (MkUnifyResult [] holesSolved) <- tryUnify 
                                                     env 
                                                     target
                                                     !(quote defs env tm)
        | _ => none 
       case nty of
            Bound => case defined n env of
                          Nothing => throw (GenericMsg "Bound not in env")
                          (Just (MkIsDefined p)) => pure $ [Local _ p]
            _ => pure $ [Ref nty n]
       

structuralRecursionCheck : {vars :_} ->
                           {auto c : Ref Ctxt Defs} ->
                           {auto u : Ref UST UState} ->
                           Env Term vars -> RawImp -> Term vars ->
                           Core Bool
structuralRecursionCheck env lhs rhs
 = do let tm = getScope lhs
          (IVar fn, args) = getArgs tm
           | _ => throw (GenericMsg "Shouldn't happen")
          tm' = unelab rhs
          (IVar fn', args') = getArgs tm'
           | _ => throw (GenericMsg "Shouldn't happen")
      -- return true if they are different
      pure $ if fn == fn' 
                then checkArgs args (reverse args')
                else True
 where getScope : RawImp -> RawImp
       getScope (IPatvar x ty scope) = getScope scope
       getScope tm = tm

       getArgs : RawImp -> (RawImp , List RawImp)
       getArgs (IApp f a) = let (f', as) = getArgs f in (f' , a :: as)
       getArgs lhs = (lhs, [])

       nameIn : Name -> RawImp -> Bool
       nameIn n (IVar x) = n == x
       nameIn n (IApp x y) = nameIn n x || nameIn n y
       nameIn n _ = True

       checkArgs : List RawImp -> List RawImp -> Bool
       checkArgs ls ((IVar x) :: rs)
         = case filter (nameIn x) ls of
             [] => True
             (y :: xs) => checkArgs ls rs
       checkArgs ls ((IApp x y) :: rs) 
        = checkArgs ls [x] || checkArgs ls [y]
       checkArgs ls (_ :: rs) = checkArgs ls rs
       -- we have reached the end and none have been different
       checkArgs ls [] = False



tryDef : {vars : _} ->
         {auto c : Ref Ctxt Defs} -> 
         {auto u : Ref UST UState} ->
         Search vars -> Name -> NameType ->
         Term [] -> Core (List (Term vars))
tryDef s@(MkSearch depth name env lhs target) n nty tm 
 = do defs <- get Ctxt 
      norm <- nf defs env (rewrite sym (appendNilRightNeutral vars) 
                                in weakenNs vars tm)
      (ntm , args) <- fillMetas env norm
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
tryLocals s@(MkSearch (S depth) name env lhs target) (l@(Local idx p) :: usable)
    = case !(tryUnify env target (binderType $ getBinder p env)) of 
        Just (MkUnifyResult [] holesSolved) => 
              pure (Local idx p :: !(tryLocals s usable))
        _ => case (binderType $ getBinder p env) of 
                  fn@(Bind x (Pi y z w) scope) => 
                   do defs <- get Ctxt
                      (filled, metas) <- fillMetas env 
                                                   !(nf defs env fn)
                      Just ures <- tryUnify env 
                                            target
                                            !(quote defs env filled)
                        | _ => tryLocals s usable   
                      pure $
                       !(tryIfSuccessful s (nameAt idx p) Bound !(nf defs env fn))
                         ++ !(tryLocals s usable)
                  _ => tryLocals s usable
tryLocals s@(MkSearch Z name env lhs target) (l@(Local idx p) :: usable)
    = case !(tryUnify env target (binderType $ getBinder p env)) of 
        Just (MkUnifyResult [] holesSolved) => 
              pure (Local idx p :: !(tryLocals s usable))
        _ => tryLocals s usable
tryLocals _ _ = none


synthesise s@(MkSearch depth name env lhs (Bind n (Pi n' pinfo tm) scope)) 
 = pure $ !(tryLocals s (getUsableEnv [] env)) ++ (map (Bind n (Lam n' pinfo tm))
              !(synthesise (MkSearch depth n (Lam n' pinfo tm :: env) lhs scope)))
synthesise s@(MkSearch d name env lhs TType) 
  = pure $ !(tryLocals s (getUsableEnv [] env)) 
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
      if name == (UN "v92") then do traverse (log . show) fs ; pure () else pure ()
      --pure $ sortBy (sort s) (locals ++ cons ++ fs)
      pure $ (locals ++ cons ++ fs)

synthesiseWorlds : {auto c : Ref Ctxt Defs} -> 
                   {auto u : Ref UST UState} -> 
                   Name ->
                   List (vars ** (Env Term vars , Term vars, RawImp)) ->
                   Core (Maybe (List (Clause, RawImp, RawImp)))
synthesiseWorlds n [] = pure $ Just []
synthesiseWorlds n ((vars ** (env, tm, ri)) :: xs)
 = do let s = (MkSearch 4 n env ri tm)
      (t :: ts) <- synthesise s | _ => nothing  
      (t' :: ts') <- filterM (structuralRecursionCheck env ri) (t :: ts) | _ => nothing
      Just rest <- synthesiseWorlds n xs | _ => nothing
      clause <- getClause (s, t', ri)
      pure $ Just (clause :: rest)


containsBaseCase : List RawImp -> Name -> Core Bool
containsBaseCase [] n = pure False
containsBaseCase ((IApp x y) :: xs) n = if n == !(headName x)
                                           then containsBaseCase xs n
                                           else pure True
  where headName : RawImp -> Core Name
        headName (IVar z) = pure z
        headName (IApp z w) = headName z
        headName _ = throw (GenericMsg "Invalid expression at head of synthesised term")
containsBaseCase _ _ = pure True

synthesisePM : {auto c : Ref Ctxt Defs} -> 
               {auto u : Ref UST UState} ->
               Name -> Term []->
               List (vars ** (Env Term vars , Term vars, RawImp)) ->
               Core (Maybe (Def, List (Clause, RawImp, RawImp)))
synthesisePM n ty ss
  = do Just clauses <- synthesiseWorlds n ss | _ => nothing
       True <- containsBaseCase (map (\ (_, (_,a)) => a) clauses) n | _ => nothing
       (as ** ct) <- getPMDef n ty $ map (\ (a,_,_) => a) clauses
       pure $ Just (PMDef as ct, clauses)


getLhs : {vars :_} -> {auto c : Ref Ctxt Defs} -> Term vars -> Name -> List RawImp -> RawImp 
getLhs (Bind x (Pi m pinfo tm) scope) n ls 
  = let tm' = unelab tm
        sc = getLhs scope n ((IVar m) :: ls) in
         IPatvar x tm' sc
getLhs tm n ls = apply (IVar n) (reverse ls)

defSearch : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} -> 
        GlobalDef -> Name -> List RawImp -> Nat ->
        Core (Maybe (Def, List (Clause, RawImp, RawImp)))
defSearch def n lhs splits = 
  do cs@(c :: cases) <- traverse (\ l => splitLhs False splits [] l) lhs 
      | _ => pure Nothing
     gs@(p :: ps) <- filterCheckable (map (\ a => (a,[])) (concat cs))
      | _ => pure Nothing
     Just res <- synthesisePM n (type def)
                  !(traverse (\ (_,gd,ri,_) => 
                           pure $ getSearchData !(getTerm gd) [] ri) gs)
      | _ => defSearch def n (map (\ (_,_,ri,_) => ri) gs) (S splits) 
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
                  case !(defSearch def n [getLhs (type def) n []] 0) of
                    Just (res, clauses) => 
                      pure $ resugarType clauses n $ unelab (type def)
                    Nothing  => pure "No match"
               (MetaVar vars env retTy) => 
                do let Just lhs = lookup n (userholes ust)
                     | _ => pure "Missing hole"
                   rs <- synthesise (MkSearch 4 n env lhs retTy) 
                   (r :: rs') <- filterM 
                                  (structuralRecursionCheck env lhs)
                                  rs
                    | _ => pure "No match"
                   -- here we want to add in some heuristic for sorting
                   pure $ resugar $ unelab r
               _ => pure "Invalid definition"



