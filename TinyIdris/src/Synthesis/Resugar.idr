module Synthesis.Resugar 

import Data.Strings

import TTImp.TTImp

import Core.TT
import Synthesis.Monad

import Data.Strings
import Data.List

mutual
resugarPat : Name ->
             (pat : RawImp) ->
             (scope : RawImp) ->
             (first : Bool) ->
             String
resugarPat x pat scope True 
  = "pat " ++ resugarPat x pat scope False
resugarPat x pat (IPatvar y ty scope) False 
  = show x ++ " : " ++ resugar pat ++ " , " ++ resugarPat y ty scope False
resugarPat x pat scope False
  = show x ++ " : " ++ resugar pat ++ " => " ++ resugar scope

resugarLam : (first : Bool) ->
             (Maybe Name) ->
             (scope : RawImp) -> 
             String
resugarLam True x scope 
  = "lam " ++ resugarLam False x scope 
resugarLam False Nothing (ILam y z argTy scope) 
  = " _ " ++ resugarLam False z scope 
resugarLam False (Just (UN x)) (ILam y z argTy scope) 
  = x ++ " " ++ resugarLam False z scope 
resugarLam False (Just (MN x w)) (ILam y z argTy scope) 
  = "_ " ++ " " ++ resugarLam False z scope 
resugarLam False Nothing scope 
  = " _ => " ++ resugar scope 
resugarLam False (Just (UN x)) scope 
  = x ++ " => " ++ resugar scope
resugarLam False (Just (MN x y)) scope
  = "_ " ++ " => " ++ resugar scope

export
resugar : RawImp -> String
resugar (IVar (UN x)) = x
resugar (IVar (MN x y)) = "_"
resugar (IPi x Nothing argTy scope) 
  = " ( _ : " ++ resugar argTy ++ ") -> " ++ resugar scope
resugar (IPi x (Just (UN y)) argTy scope) 
  = " ( " ++ y ++ " : " ++ resugar argTy ++ " ) -> " ++ resugar scope
resugar (IPi x (Just (MN y z)) argTy scope)
  = " ( _ : " ++ resugar argTy ++ " ) -> " ++ resugar scope 
resugar (ILam x y argTy scope) = resugarLam True y scope 
resugar (IPatvar x ty scope) = resugarPat x ty scope True
resugar (IApp x y) 
  = let (f , as) = getFnArgs x in 
        "(" ++ (resugar f) ++ " " ++ (resugar y) ++ " " ++ (concat $ intersperse " " (map resugar as)) ++ ")"
  where getFnArgs : RawImp -> (RawImp , List (RawImp))
        getFnArgs (IApp z w) = let (f , args) = getFnArgs z in (f , (w :: args))
        getFnArgs fn = (fn , [])
resugar (IHole (UN x)) = "?" ++ x
resugar (IHole (MN x y)) = "?_"
resugar Implicit = "_"
resugar IType = " : "

