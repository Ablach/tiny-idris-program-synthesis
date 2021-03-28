{-
Module: Synthesis.CaseSplit 
Author: Scott Mora
Last Modified: 27.03.2021
Summary: This module provides functionality for 
generating pattern matchin definitions when 
proivided with a term to split, and environment in 
which it should be split. 
-}
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

{-
FixUpScope: Traverses a given RawImp 
term, replacing each occurance of a given 
name with a replacement term, 
-}
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
   where
      fus : Name -> RawImp -> RawImp -> (RawImp, Bool)
      fus n (IVar y) rep 
       = if n == y then (rep, True) else (IVar y, False)
      fus n (IApp y z) rep = let (f, inf) = fus n y rep
                                 (a, ina) = fus n z rep in
                             (IApp f a, inf || ina)
      fus n tm rep = (tm, False)
fixUpScope n tm rep = (tm, [])


{-
getData: Looks up the definition of a 
given data constructor name, 
returning the name, type, tag and arity.
-}
getData : {auto c : Ref Ctxt Defs} ->
          Name ->
          Core (Name, Term [], Int, Nat)
getData n 
 = do defs <- get Ctxt
      Just def <- lookupDef n defs | _ => throw (NotInContext n)
      let (DCon tag arity) = definition def 
        | _ => throw (InvalidDefinition n)
      pure (n, (type def), tag, arity)


{-
validCon: Checks if a given data constructor 
unifies with a given return type, returning 
a boolean success value. 
-}
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
                      !(quote defs env filled)
                      !(quote defs env (NTCon tyn tytag tyar tyargs))
      deleteMetas metas
      case res of
       Nothing => pure False
       Just _ => pure True

{-
The following three functions check whether 
a given name is present within list 
of closures, paired with an accompanying closure.
If the name is found, a term from the paired 
closure is returned.

This is used when attermpting to fill in any 
arguments to a data constructor whos value 
is present within the resulting type. 
-}
lookupTm : {vars : _} ->
           {vars' : _} ->
           Name ->
           (Term (vars), Term vars') ->
           Maybe (RawImp)
lookupTm n ((Local idx p), (Local idx' p'))
  = if n == (nameAt idx p)
       then Just (IVar $ nameAt idx' p')
       else Nothing
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
           
{-
getSplitData:  generates a list of 
closure x closure pairs from a given 
data constructor, and a list of 
closures passed in.
-}

getSplitData : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               NF vars -> Env Term vars ->
               List (Closure vars) -> NF vars ->
               Core (List (Closure vars, Closure vars), NF vars)
getSplitData (NBind x y f) env cs og 
  = getSplitData !(f !(get Ctxt) 
                  (toClosure env !(quote !(get Ctxt) 
                                         env 
                                         (binderType y))))
                  env cs og
getSplitData (NTCon x tag arity xs) env cs og 
  = pure (zip xs cs, og)
getSplitData tm env cs og = pure ([], og)


{-
getRaw: When provided with a data constructor 
term, generate pattern variables taking in 
each argument that is not currently known, 
and the application of the constructor to 
all of it's required arguments.


splits and depth naturals are used for 
constructing unique names for each 
argument generated.
-}
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
                !(getRaw splits
                         (S depth)
                         env
                         (IVar nm :: rs)
                         dcn
                         (cs, f'))
         Just (x, clo@(MkClosure _ _ tm)) =>
           getRaw splits depth env (x :: rs) dcn (cs, !(f defs clo))
getRaw splits depth env rs dcn (x, tm)
 = pure $ apply (IVar dcn) (reverse rs)

{-
splitPats: Given a RawImp term, split it into two 
sections, the pattern variables, and the resulting 
application.
-}
splitPats : RawImp -> ((RawImp -> RawImp), RawImp)
splitPats (IPatvar x ty scope)
  = let (pats, ret) = splitPats scope in
        ((\ z => IPatvar x ty (pats z)), ret)
splitPats tm = (id, tm)

{-
The following two functions are used to fill
in all implicit arguments with their 
expected type, where possible. Operates 
as a stripped down elabouration, replacing 
any implicits for which we have a value. 
-}
replaceImplicitAt : {vars :_} -> 
                    {auto c : Ref Ctxt Defs} -> 
                    {auto u : Ref UST UState} ->
                    Name -> Term vars -> RawImp -> RawImp
replaceImplicitAt n tm (IPatvar x Implicit scope) 
  = if n == x 
       then IPatvar x (unelab tm) scope
       else IPatvar x Implicit (replaceImplicitAt n tm scope)
replaceImplicitAt n tm (IPatvar x y scope) 
  = IPatvar x y (replaceImplicitAt n tm scope)
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
      

{-
getSplit: Tests if a given type constructor 
can be constructed by only one valid data 
constructor, performing a split if this is 
the case.                                   
-}
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
             getSplit splits 
                      !(sc defs 
                           (toClosure env 
                           !(quote defs env (binderType b)))) n env
getSplit splits tm n env = nothing

{-
splitOnN: Given a name and a term, if the name is 
present within the terms patterns, split 
the term into the patterns occuring before
the name, and everything that comes after. 
-}
splitOnN : RawImp -> Name -> (Maybe (RawImp -> RawImp), RawImp)
splitOnN (IPatvar x ty scope) n 
  = if x == n 
       then (Nothing, scope)
       else case splitOnN scope n of 
                 (Nothing, z) => (Just (IPatvar x ty), z)
                 ((Just y), z) =>
                    (Just (\ sc' => IPatvar x ty (y sc')), z)
splitOnN tm n = (Nothing, tm)


{-
envToPat: Given an environment filled by pattern variables, 
construct a RawImp term taking in those variables. 

Environents generated will always only contain pattern 
variables, therefore the impossible state will never 
be reached. 
-}
envToPat : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Env Term vars ->
           RawImp -> RawImp
envToPat [] r = r
envToPat ((PVar x z) :: env) r = envToPat env $ IPatvar x (unelab z) r 
envToPat (_ :: env) r = ?impossible_state



{-
splitSingles: Given a left hand side term and a name, 
test if any names can be split into an individual 
data constructor, carrying out the split if so. 

Any names that depend on successful splits are 
added to the list, the process repeats until the 
list is empty.
-}
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
               let (Just pre, suf) = splitOnN (IPatvar x ty scope) n
                 | _ => none
               let front = pre . pats 
                   (newsc, names) = fixUpScope n suf app
               newtm <- fillImplicits (front newsc) [] (front newsc) 
               pure [(newtm, names)] 
        splitSingle _ _ = none

{-
getConPatterns: Given a name, term and data constructor
replace get the required patterns, replace each occurance
of the name with the new term, and merge the results with 
the initial term.
-}
getConPatterns : {vars : _} ->
                 {auto c : Ref Ctxt Defs} -> 
                 {auto u : Ref UST UState} ->
                 Nat -> RawImp -> Env Term vars ->
                 List (Closure vars) -> Name -> 
                 Name -> Core (RawImp, List Name)
getConPatterns splits ri env cs name n
   = do defs <- get Ctxt
        Just def <- lookupDef n defs
         | _ => throw (NotInContext n)
        let (DCon t a) = definition def
         | _ => throw (InvalidDefinition n)
        norm <- nf defs env (rewrite sym (appendNilRightNeutral vars)
                                  in weakenNs vars $ type def)
        dst <- getSplitData norm env cs norm
        raw <- getRaw splits 0 env [] n dst
        let (pats, app) = splitPats raw 
        let (front, back, names)
           = case splitOnN ri name of
                (Nothing, suf) => 
                  ((envToPat env) . pats, fixUpScope name suf app)      
                ((Just pre), suf) => 
                  ((envToPat env) . pre . pats, fixUpScope name suf app)
        newtm <- fillImplicits (front back) [] (front back) 
        pure (newtm, names) 

{-
splitLhs: Interaction point of the module,
given a name, term and environment, split 
the first possible term, if this forces 
any other splits, perform them. Returns 
the list of new left hand sides.
-}
        
export
splitLhs : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           Bool -> Nat -> Env Term vars -> RawImp -> 
           Core (List RawImp)
splitLhs in_split splits env (IPatvar x ty scope)
  = do defs <- get Ctxt
       (tm , gtm) <- checkTerm env ty Nothing  
       let (IVar n) = getFn ty | _ => cont x tm
       Just def <- lookupDef n defs | _ => cont x tm 
       let (TCon tag arity datas) = definition def | _ => cont x tm
       (NTCon _ _ _ cs) <- nf defs env tm
         | _ => throw (GenericMsg "TCon not normalising to NTCon")
       spt <- traverse 
            (getConPatterns splits (IPatvar x ty scope) env cs x) datas
       finals <- traverse (splitSingles (S splits)) spt
       pure $ concat finals
   where 
     cont : Name -> Term vars -> Core (List RawImp)
     cont x tm = if in_split 
                     then pure []
                     else 
                      splitLhs {vars = (x :: vars)}
                               in_split
                               splits
                               (PVar x tm :: env)
                               scope
splitLhs _ _ _ _ = none


