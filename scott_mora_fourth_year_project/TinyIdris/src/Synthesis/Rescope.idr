{-
Module: module Synthesis.Rescope 
Author: Scott Mora
Last Modified: 28.03.2021
Summary: The functionallity presented here 
allows an environment to be converted into 
a list of local variables, where the binders
are lambdas or pattern variables. 
-}

module Synthesis.Rescope 

import Core.Env
import Core.TT
import Core.Core

import Data.List
  
givenName : Name -> Bool
givenName (UN x) = True
givenName _      = False

{-
The following two functions are used to wekaen the 
names in scope. The list of names passed to the 
getUsableEnv function will be used to weaken terms, 
proofs of associativity are required to satisfy the 
type checker that the list of names are in fact equal.
-}
weakenMore : (xs : List Name) -> (p : IsVar n i top) ->
             IsVar n (length xs + i) (xs ++ top)
weakenMore [] p = p
weakenMore (x :: xs) p = Later (weakenMore xs p)

weakenNS : (ns : List Name) -> Var top -> Var (ns ++ top)
weakenNS [] p                = p
weakenNS (x :: xs) (MkVar p) = MkVar (Later $ weakenMore xs p)

export
getUsableEnv : {vars : _} -> 
               (ns : List Name) ->
               Env Term vars ->
               List (Term (ns ++ vars))
getUsableEnv {vars = v :: vars} ns ((Lam n z w) :: env) 
= let rest = getUsableEnv {vars = vars} (ns ++ [v]) env 
      MkVar var = weakenNS ns (MkVar First) in
  Local _ var :: rewrite appendAssociative ns [v] vars in rest
getUsableEnv {vars = v :: vars} ns ((PVar x z) :: env) 
= let rest = getUsableEnv {vars = vars} (ns ++ [v]) env 
      MkVar var = weakenNS ns (MkVar First) in 
  Local _ var :: rewrite appendAssociative ns [v] vars in rest
getUsableEnv {vars = v :: vars} ns (_ :: env) 
  = rewrite appendAssociative ns [v] vars in getUsableEnv (ns ++ [v]) env
getUsableEnv _ [] = []
