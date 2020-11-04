module Synthesis.Resugar 

import Data.Strings

import TTImp.TTImp

import Core.TT


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

resugarLam : (Maybe Name) ->
             (scope : RawImp) -> 
             (first : Bool) ->
             String
resugarLam x scope True
  = "\ " ++ resugarLam x scope False
resugarLam Nothing (ILam y z argTy scope) False
  = " _ " ++ resugarLam z scope False
resugarLam (Just x) (ILam y z argTy scope) False
  = show x ++ " " ++ resugarLam z scope False
resugarLam Nothing scope False
  = " _ => " ++ resugar scope 
resugarLam (Just x) scope False
  = show x ++ " => " ++ resugar scope

export
resugar : RawImp -> String
resugar (IVar x) = show x
resugar (IPi x Nothing argTy scope) 
  = " ( _ : " ++ resugar argTy ++ ") -> " ++ resugar scope
resugar (IPi x (Just y) argTy scope) 
  = " ( " ++ show y ++ " : " ++ resugar argTy ++ " ) -> " ++ resugar scope
resugar (ILam x y argTy scope) = resugarLam y scope True
resugar (IPatvar x ty scope) = resugarPat x ty scope True
resugar (IApp x y) = "( " ++ (resugar x) ++ " " ++ resugar y ++ " )"
resugar (IHole x) = "?" ++ show x
resugar Implicit = "_"
resugar IType = " : "
