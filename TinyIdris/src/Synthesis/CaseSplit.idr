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
fus n (IVar y) rep = if n == y then (rep, True) else (IVar y, False)
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
  = do nm <- genName $ "x" ++ (show splits) ++ "_" ++ (show (S k))
       ns <- genNames k splits
       pure (nm :: ns)

toPatVar : List Name -> RawImp -> RawImp
toPatVar [] ri = ri
toPatVar (n :: ns) ri = IPatvar n Implicit (toPatVar ns ri)

getConPatterns :  {auto c : Ref Ctxt Defs} -> 
                  {auto u : Ref UST UState} ->
                  Nat -> Name -> Core (RawImp, (RawImp -> RawImp))
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
           Bool -> Nat -> RawImp -> Core (List (RawImp, List Name))
splitLhs in_split splits (IPatvar x ty scope)  
  = do defs <- get Ctxt
       let (IVar n) = getFn ty | _ => cont
       Just def <- lookupDef n defs | _ => cont
       let (TCon tag arity datas) = definition def | _ => cont
       pats <- traverse (getConPatterns splits) datas
       let finals = map (\ (fs, sn) => ((fixUpScope x scope fs) , sn)) pats
       pure $ merge finals
     
       -- for each data constructor,  remove the pattern for n, and add patterns for their 
       -- args, then a : _ ect, then apply f (constructor a..an) args...
   where 
         cont : Core (List (RawImp, List Name)) 
         cont = if in_split 
                   then pure []
                   else do (r :: rs) <- splitLhs in_split splits scope | _ => none
                           pure $ map (\ (sc, ns) => ((IPatvar x ty sc), ns)) (r :: rs)
splitLhs _ _ _ = none


getData : {auto c : Ref Ctxt Defs} -> Name -> Core (Name, Term [], Int, Nat)
getData n = do defs <- get Ctxt
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
       (filled, metas) <- fillMetas env !(nf defs env (rewrite sym (appendNilRightNeutral vars) in weakenNs vars datatm)) 
       res <- tryUnify env !(quote defs env filled) !(quote defs env (NTCon tyn tytag tyar tyargs))
       deleteMetas metas
       case res of
          Nothing => pure False
          Just _ => pure True

getI : Term vars -> Maybe Nat
getI (Local idx p) = Just idx
getI _ = Nothing

getIdx : {vars : _} -> Term vars -> List Nat
getIdx (Bind x y scope) = getIdx scope
getIdx tm = let (fn, as) = getFnArgs tm in filterJust $ map getI as

getArgs : {vars : _} -> 
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          Nat -> Term vars -> Env Term vars ->
          Core (List (Either Nat (RawImp -> RawImp)))
getArgs n (Bind x y scope) env 
 = case elem n (getIdx scope) of
    True => pure (Left n :: !(getArgs (S n) scope (y :: env)))
    False => 
     pure ((Right $ (IPatvar x (unelab (binderType y)))) :: !(getArgs (S n) scope (y :: env)))
getArgs n _ env = pure []

showEi : List (Either Nat (RawImp -> RawImp)) -> Core ()
showEi [] = pure ()
showEi ((Left x) :: xs) = do log $ show x ; showEi xs
showEi ((Right x) :: xs) = do log $ resugar $ x (IHole (UN "bum")) ; showEi xs

getSplit : {vars : _} -> 
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           NF vars -> Name -> Env Term vars ->
           Core (Maybe (Name, Term [], Int, Nat))
getSplit val@(NBind x b sc) n env =
  if x == n
     then do defs <- get Ctxt
             let tm = binderType b
             let (NTCon y tag arity xs) = binderType b | _ => nothing
             Just def <- lookupDef y defs | _ => throw (NotInContext n)
             let (TCon tag' arity' datas) = definition def | _ => throw (InvalidDefinition y)
             datacons <- traverse getData datas
             [valid] <- filterM (validCon val n env y tag arity xs) datacons             
              | _ => nothing 
             let (a,b,d,e) = valid
             log $ show b
             res <- getArgs 0 b []
             showEi res
             pure $ Just valid
     else do defs <- get Ctxt 
             getSplit !(sc defs (toClosure env !(quote defs env (binderType b)))) n env
getSplit tm n env = nothing

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

export
splitSingles : {auto c : Ref Ctxt Defs} -> 
               {auto u : Ref UST UState} ->
               Nat -> (RawImp, List Name) -> 
               Core (List RawImp)
splitSingles splits (tm,[]) = pure [tm]
splitSingles splits (tm,(n :: ns)) 
  = do upd <- splitSingle tm n 
       [(_,_,updated, newnames)] <- filterCheckable upd | _ => splitSingles splits (tm, ns)
       splitSingles (S splits) (updated, ns ++ newnames)
  where  
        splitSingle : RawImp -> Name -> Core (List (RawImp, List Name))
        splitSingle (IPatvar x ty scope) n
          = do defs <- get Ctxt
               (tm , gd) <- checkTerm [] (IPatvar x ty scope) Nothing
               norm <- nf defs [] tm
               Just (dcn, dctm, tag, arity) <- getSplit norm n [] | _ => none
               let (Just pre, suf) = splitOnN (IPatvar x ty scope) n | _ => none
               ns <- genNames arity splits
               let ns' = map IVar ns
                   rawdata = apply (IVar dcn) ns' 
                   rest = tpv dctm 0 splits 
                   (newsc, names) = fixUpScope n suf rawdata 
               pure [(pre $ !(rest $ newsc), names)]
        splitSingle _ _ = none


