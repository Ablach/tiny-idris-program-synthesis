{-
Module: Synthesis.Resugar
Author: Scott Mora
Last Modified: 28.03.2021
Summary: Provides functionallity for
resugaring RawImp terms back to TinyIdris
syntax. Individual terms may be resugared,
or full pattern matching definitions.
-}

module Synthesis.Resugar 

import TTImp.TTImp
import Core.TT
import Core.Context
import Core.CaseTree
import Core.Env

import Synthesis.Unelab

import Data.Strings
import Data.List

showN : Name -> String
showN (UN x) = x
showN (MN x y) = x 

getFnArgs : RawImp -> (RawImp , List (RawImp))
getFnArgs (IApp z w) = let (f , args) = getFnArgs z in (f , (w :: args))
getFnArgs fn = (fn , [])

{-
Helper function have been generated to resugar patterns, lambdas, 
pi's, and applications due to them being presented differently based
on their position. To perform all of this the resugar function is 
called, which uses the resugar' function to handle the helpers.
-}
mutual
resugarLHS : Bool -> RawImp -> String
resugarLHS False (IApp x a )
  = let (f , as) = getFnArgs (IApp x a) in 
        "(" ++ (resugarLHS False f) ++ " " ++ (concat $ intersperse " " (map (resugarLHS False) (reverse as))) ++ ")"
resugarLHS True (IApp x a)
  = let (f , as) = getFnArgs (IApp x a) in 
        (resugarLHS False f) ++ " " ++ (concat $ intersperse " " (map (resugarLHS False) (reverse as)))
resugarLHS b tm = resugar' tm 

resugarPat : Name ->
             (pat : RawImp) ->
             (scope : RawImp) ->
             (first : Bool) ->
             String
resugarPat x pat scope True 
  = "pat " ++ resugarPat x pat scope False
resugarPat x pat (IPatvar y ty scope) False 
  = (showN x) ++ " : " ++ resugarLHS True pat ++ ", " ++ resugarPat y ty scope False
resugarPat x pat scope False
  = (showN x) ++ " : " ++ resugarLHS True pat ++ " =>\n   " ++ resugarLHS True scope

resugarLam : (first : Bool) ->
             (Maybe Name) ->
             (scope : RawImp) -> 
             String
resugarLam True x scope 
  = "lam " ++ resugarLam False x scope 
resugarLam False Nothing (ILam y z argTy scope) 
  = "_ " ++ resugarLam False z scope 
resugarLam False (Just x) (ILam y z argTy scope) 
  = (showN x) ++ " " ++ resugarLam False z scope 
resugarLam False Nothing scope 
  = " _ => " ++ resugar' scope 
resugarLam False (Just x) scope 
  = (showN x) ++ " => " ++ resugar' scope

resugarApp : RawImp -> RawImp -> String
resugarApp x a
  = let (f , as) = getFnArgs (IApp x a) in 
        (resugar' f) ++ " " ++ (concat $ intersperse " " (reverse $ map resugar' as))
  where getFnArgs : RawImp -> (RawImp , List (RawImp))
        getFnArgs (IApp z w) = let (f , args) = getFnArgs z in (f , (w :: args))
        getFnArgs fn = (fn , [])


resugar' : RawImp -> String
resugar' (IVar x) = showN x
resugar' (IPi x Nothing argTy scope) 
  = "(_ : " ++ resugar' argTy ++ ") -> " ++ resugar' scope
resugar' (IPi x (Just (UN y)) argTy scope) 
  = "(" ++ y ++ " : " ++ resugar' argTy ++ ") -> " ++ resugar' scope
resugar' (IPi x (Just (MN y z)) argTy scope)
  = "(_ : " ++ resugar' argTy ++ ") -> " ++ resugar' scope 
resugar' (ILam x y argTy scope) = resugarLam True y scope 
resugar' (IPatvar x ty scope) = resugarPat x ty scope True
resugar' (IApp x y) = "(" ++ (resugarApp x y) ++ ")"
resugar' (IHole (UN x)) = "?" ++ x
resugar' (IHole (MN x y)) = "?_"
resugar' Implicit = "_"
resugar' IType = "Type"

export
resugar : RawImp -> String
resugar (IApp x y) = resugarApp x y
resugar tm = resugar' tm

{-
Resugaring definitions consists of resugaring the type signature, followed by
each clause, and combining the results.
-}
resugarClauses : {auto c : Ref Ctxt Defs} -> List (Clause, RawImp, RawImp) -> String
resugarClauses [] = ""
resugarClauses ((_, (l, r)) :: xs) 
  = (resugar l) ++ " = " ++ (resugar r) ++ "\n" ++ resugarClauses xs

export
resugarType : {auto c : Ref Ctxt Defs} -> List (Clause, RawImp, RawImp) -> Name -> RawImp -> String
resugarType cs (UN n) ty = n ++ " : " ++ (resugar ty) ++ "\n" ++ resugarClauses cs
resugarType cs (MN n m) ty = n ++ " : " ++ (resugar ty) ++ "\n" ++ resugarClauses cs
