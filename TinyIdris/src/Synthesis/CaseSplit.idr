module Synthesis.CaseSplit 

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


import Data.List
import Data.Nat
import Data.Maybe
import Data.Either
import Data.SortedMap

import Synthesis.Util
import Synthesis.Resugar
import Synthesis.Unelab

merge : List ((a, ns) , a -> b) -> List (b, ns)
merge = map (\ ((fs, ns), sn) => (sn fs, ns)) 

fus : Name -> RawImp -> RawImp -> (RawImp, Bool)
fus n (IVar y) rep 
 = if n == y then (rep, True) else (IVar y, False)
fus n (IApp y z) rep = let (f, inf) = fus n y rep
                           (a, ina) = fus n z rep in
                       (IApp f a, inf || ina)
fus n tm rep = (tm, False)


fixUpScope : Name ->
             (scope : RawImp) ->
             (replacement : RawImp) ->
             (RawImp, List Name)
fixUpScope n (IVar x) rep 
 = if x == n then (rep, []) else (IVar x, [])
fixUpScope n (IApp f tm) rep 
 = (IApp (fst $ fixUpScope n f rep) (fst $ fixUpScope n tm rep), [])
fixUpScope n (IPatvar y z w) rep 
 = let (tm, b) = fus n z rep
       (sc, rest) = fixUpScope n w rep
       rest' = if b then (y :: rest) else rest in 
   (IPatvar y tm sc, rest')
fixUpScope n tm rep = (tm, [])

genNames : {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           Nat -> Nat -> Core (List Name)
genNames Z splits = none
genNames (S k) splits 
  = do nm <- genName $ "x" ++ (show splits) ++ (show (S k))
       ns <- genNames k splits
       pure (nm :: ns)

toPatVar : List Name -> RawImp -> RawImp
toPatVar [] ri = ri
toPatVar (n :: ns) ri = IPatvar n Implicit (toPatVar ns ri)

getConPatterns :  {auto c : Ref Ctxt Defs} -> 
                  {auto u : Ref UST UState} ->
                  Nat -> Name -> 
                  Core (RawImp, (RawImp -> RawImp))
getConPatterns splits n
   = do defs <- get Ctxt
        Just def <- lookupDef n defs | _ => throw (NotInContext n)
        let (DCon t a) = definition def | _ => throw (InvalidDefinition n)
        ns <- genNames a splits
        let ns' = map IVar ns
        pure $ (apply (IVar n) ns' , toPatVar ns)


export
splitLhs : {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           Bool -> Nat -> RawImp ->
           Core (List (RawImp, List Name))
splitLhs in_split splits (IPatvar x ty scope)  
  = do defs <- get Ctxt
       let (IVar n) = getFn ty | _ => cont
       Just def <- lookupDef n defs | _ => cont
       let (TCon tag arity datas) = definition def | _ => cont
       pats <- traverse (getConPatterns splits) datas
       let finals = map (\ (fs, sn) => ((fixUpScope x scope fs) , sn)) pats
       pure $ merge finals  
   where 
       cont : Core (List (RawImp, List Name)) 
       cont = if in_split 
                then pure []
                else do (r :: rs) <- splitLhs in_split splits scope | _ => none
                        pure $ map (\ (sc, ns) => ((IPatvar x ty sc), ns)) (r :: rs)
splitLhs _ _ _ = none


getData : {auto c : Ref Ctxt Defs} ->
          Name ->
          Core (Name, Term [], Int, Nat)
getData n 
 = do defs <- get Ctxt
      Just def <- lookupDef n defs | _ => throw (NotInContext n)
      let (DCon tag arity) = definition def | _ => throw (InvalidDefinition n)
      pure (n, (type def), tag, arity)


validCon : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           NF vars -> Name -> Env Term vars -> -- orginal args
           Name -> Int -> Nat -> List (Closure vars) -> --type constructor
           (Name, Term [], Int, Nat) -> -- data constructor 
           Core Bool
validCon val n env tyn tytag tyar tyargs (datan, datatm, datatag, dataar)
 = do defs <- get Ctxt
      (filled, metas) <- fillMetas env 
       !(nf defs env (rewrite sym (appendNilRightNeutral vars) 
                           in weakenNs vars datatm)) 
      res <- tryUnify env 
       !(quote defs env filled) !(quote defs env (NTCon tyn tytag tyar tyargs))
      deleteMetas metas
      case res of
       Nothing => pure False
       Just _ => pure True


lookupTm : {vars : _} ->
           {vars' : _} ->
           Name ->
           (Term (vars), Term vars') ->
           Maybe (RawImp)
lookupTm n ((Local idx p), (Local idx' p'))
  = if n == (nameAt idx p) then Just (IVar $ nameAt idx' p') else Nothing
lookupTm n ((App x z), (App x' z'))
  = lookupTm n (x,x') <|> lookupTm n (z,z')
lookupTm n _ = Nothing

lookupLTm : {vars : _} ->
            {vars' : _} ->
            Name ->
            List ((Term vars), (Term vars')) ->
            Maybe (RawImp)
lookupLTm n [] = Nothing
lookupLTm n (((Local idx p), (Local idx' p')) :: xs) 
  = if n == (nameAt idx p)
       then Just (IVar (nameAt idx' p'))
       else lookupLTm n xs
lookupLTm n (tm :: xs) = lookupTm n tm <|> lookupLTm n xs

lookupClos : {vars :_} ->
             {auto c : Ref Ctxt Defs} ->
             List (Closure vars, Closure vars) ->
             Name ->
             Maybe (RawImp, Closure vars)
lookupClos [] n = Nothing
lookupClos (((MkClosure x z (Local idx p)), c@(MkClosure x' z' (Local idx' p'))) :: xs) n
  = if n == (nameAt idx p)
     then Just (IVar (nameAt idx' p'), c)
     else lookupClos xs n
lookupClos ((c@(MkClosure x z tm), (MkClosure x' z' tm')) :: xs) n 
  = let (_, as) = getFnArgs tm 
        (_, as') = getFnArgs tm'
        as'' = zip as as'
        in
        case lookupLTm n as'' of
            Nothing => lookupClos xs n
            (Just y) => Just (y, c)
           
getSplitData : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               NF vars -> Env Term vars -> List (Closure vars) -> NF vars ->
               Core (List (Closure vars, Closure vars), NF vars)
getSplitData (NBind x y f) env cs og 
  = getSplitData !(f !(get Ctxt) 
                  (toClosure env !(quote !(get Ctxt) env (binderType y))))
                  env cs og
getSplitData (NTCon x tag arity xs) env cs og 
  = pure (zip xs cs, og)
getSplitData tm env cs og = pure ([], og)

getRaw : {vars :_} -> 
         {auto c : Ref Ctxt Defs} -> 
         {auto u : Ref UST UState} ->
         Nat -> Nat -> Env Term vars -> List RawImp -> Name ->
         (List (Closure vars, Closure vars), NF vars) ->
         Core RawImp
getRaw splits depth env rs dcn (cs, (NBind y z f)) =
  do defs <- get Ctxt
     qtz <- quote defs env (binderType z)
     f' <- (f defs (toClosure env qtz))
     case lookupClos cs y of 
         Nothing => 
          do nm <- genName $ "ic" ++ (show splits) ++ (show depth)  
             pure $
              IPatvar nm Implicit 
                !(getRaw splits (S depth) env (IVar nm :: rs) dcn (cs, f'))
         Just (x, clo@(MkClosure _ _ tm)) => getRaw splits depth env (x :: rs) dcn (cs, !(f defs clo))
getRaw splits depth env rs dcn (x, tm)
 = pure $ apply (IVar dcn) (reverse rs)


splitPats : RawImp -> ((RawImp -> RawImp), RawImp)
splitPats (IPatvar x ty scope)
  = let (pats, ret) = splitPats scope in
        ((\ z => IPatvar x ty (pats z)), ret)
splitPats tm = (id, tm)

replaceImplicitAt : {vars :_} -> 
                    {auto c : Ref Ctxt Defs} -> 
                    {auto u : Ref UST UState} ->
                    Name -> Term vars -> RawImp -> RawImp
replaceImplicitAt n tm (IPatvar x Implicit scope) 
  = if n == x 
       then IPatvar x (unelab tm) scope
       else IPatvar x Implicit (replaceImplicitAt n tm scope)
replaceImplicitAt n tm (IPatvar x y scope) = IPatvar x y (replaceImplicitAt n tm scope)
replaceImplicitAt n tm ri = ri

fillImplicits : {vars :_} ->
                {auto c : Ref Ctxt Defs} -> 
                {auto u : Ref UST UState} ->
                RawImp -> Env Term vars -> RawImp -> 
                Core RawImp 
fillImplicits (IPatvar x Implicit scope) env ri
  = do (tm, gd) <- checkTerm env Implicit (Just gType)
       let env' : Env Term (x :: vars)
                = (Lam x Explicit tm :: env)
       fillImplicits scope env' ri
       
fillImplicits (IPatvar x ty scope) env ri
 = do (tm, gd) <- checkTerm env ty Nothing
      let env' : Env Term (x :: vars) 
               = (Lam x Explicit tm) :: env
      fillImplicits scope env' ri

fillImplicits (IApp f a) env ri
 = do (ftm, gfty) <- checkTerm env f Nothing
      fty <- getNF gfty
      defs <- get Ctxt
      ri' <- fillImplicits f env ri
      case fty of
       (NBind x (Pi _ _ ty) sc) => 
         do
           (atm, gaty) <- checkTerm env a
                           (Just (glueBack defs env ty))                    
           case a of 
            (IVar y) => pure $ replaceImplicitAt y !(getTerm gaty) ri'
            (IApp y z) => fillImplicits (IApp y z) env ri'
            _ => pure ri'
       t => throw (GenericMsg "Not a function type")
fillImplicits tm env ri = pure ri
      
getSplit : {vars : _} -> 
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Nat -> NF vars -> Name -> Env Term vars ->
           Core (Maybe ((RawImp -> RawImp), RawImp))
getSplit splits val@(NBind x b sc) n env =
  if x == n
     then 
      do defs <- get Ctxt
         let tm = binderType b
         let (NTCon y tag arity xs) = binderType b | _ => nothing
         Just def <- lookupDef y defs | _ => throw (NotInContext n)
         let (TCon tag' arity' datas) = definition def 
          | _ => throw (InvalidDefinition y)
         datacons <- traverse getData datas
         [valid] <- filterM (validCon val n env y tag arity xs) datacons             
          | _ => nothing 
         let (name,term,_,_) = valid 
         ntm <- nf defs env (rewrite sym (appendNilRightNeutral vars) 
                                  in weakenNs vars term)
         splitdata <- getSplitData ntm env xs ntm
         raw <- getRaw splits 0 env [] name splitdata 
         pure $ Just $ splitPats raw
     else do defs <- get Ctxt 
             getSplit splits !(sc defs 
                                  (toClosure env 
                                    !(quote defs env (binderType b)))) n env
getSplit splits tm n env = nothing

splitOnN : RawImp -> Name -> (Maybe (RawImp -> RawImp), RawImp)
splitOnN (IPatvar x ty scope) n 
  = if x == n 
       then (Nothing, scope)
       else case splitOnN scope n of 
                 (Nothing, z) => (Just (IPatvar x ty), z)
                 ((Just y), z) => (Just (\ sc' => IPatvar x ty (y sc')), z)
splitOnN tm n = (Nothing, tm)

tpv : {vars : _} ->
      {auto c : Ref Ctxt Defs} -> 
      {auto u : Ref UST UState} ->
      Term vars -> Nat -> Nat -> RawImp -> Core RawImp
tpv (Bind x y scope) n_in splits ri
  = do nm <- genName $ "x" ++ (show splits) ++ "_" ++ (show n_in)
       pure $ IPatvar nm (unelab $ binderType y) !(tpv scope (S n_in) splits ri)
tpv tm n_in splits ri = pure ri

getNonPats : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             List (Either (Nat, Name) ((RawImp -> RawImp), Name)) ->
             List (Closure vars) -> List RawImp
getNonPats [] cs = []
getNonPats ((Left (x, v)) :: xs) ((MkClosure y z w) :: ys)
  = (unelab w) :: getNonPats xs ys
getNonPats ((Right (x,n)) :: xs) cs
  = (IVar n) :: getNonPats xs cs
getNonPats _ _ = ?fdsgfdsds

export
splitSingles : {auto c : Ref Ctxt Defs} -> 
               {auto u : Ref UST UState} ->
               Nat -> (RawImp, List Name) -> 
               Core (List RawImp)
splitSingles splits (tm,[]) = pure [tm]
splitSingles splits (tm,(n :: ns)) 
  = do upd <- splitSingle tm n 
       [(_,_,updated, newnames)] <- filterCheckable upd
         | _ => splitSingles splits (tm, ns)
       splitSingles (S splits) (updated, ns ++ newnames)
  where  
        splitSingle : RawImp -> Name -> Core (List (RawImp, List Name))
        splitSingle (IPatvar x ty scope) n
          = do defs <- get Ctxt
               (tm , gd) <- checkTerm [] (IPatvar x ty scope) Nothing
               norm <- nf defs [] tm
               Just (pats, app) <- getSplit splits norm n [] | _ => none
               let (Just pre, suf) = splitOnN (IPatvar x ty scope) n | _ => none
               let front = pre . pats 
                   (newsc, names) = fixUpScope n suf app
               newtm <- fillImplicits (front newsc) [] (front newsc) 
               pure [(newtm, names)] 
        splitSingle _ _ = none


