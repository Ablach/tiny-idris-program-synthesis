{-
Module: Synthesis.Unelab
Author: Scott Mora
Last Modified: 23.03.2021
Summary: A simple conversion of 
TT terms back to RawImp.
-}

module Synthesis.Unelab 

import TTImp.TTImp
import Core.TT
import Core.Context
import Core.Env
import Core.Core


export
unelab : {vars : _} -> {auto c : Ref Ctxt Defs} -> 
         Term vars -> RawImp
unelab (Local idx prf) = IVar (nameAt idx prf)
unelab (Ref nty n) = IVar n
unelab (Meta n ts) = IHole n
unelab (Bind n (Lam nm pinfo tm) scope) 
  = ILam pinfo (Just n) (unelab tm) (unelab scope)
unelab (Bind n (Pi nm Implicit tm) scope) = Implicit
unelab (Bind n (Pi nm Explicit tm) scope)
  = IPi Explicit (Just n) (unelab tm) (unelab scope)
unelab (Bind x (PVar nm y) scope) 
  = IPatvar x (unelab y) (unelab scope)
unelab (Bind x (PVTy y) scope) = IType
unelab (App x y) = IApp (unelab x) (unelab y)
unelab TType = IType
unelab Erased = Implicit
