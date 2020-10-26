module Synthesis.Unelab 

import TTImp.TTImp
import Core.TT
import Core.Context
import Core.Env
import Core.Core

export
unelab : {vars : _} -> {auto c : Ref Ctxt Defs} -> 
         Env Term vars -> Term vars -> RawImp
unelab env (Local idx prf) = IVar (nameAt idx prf)
unelab env (Ref nty n) = IVar n
unelab env (Meta n ts) = IHole n
unelab env (Bind n (Lam pinfo tm) scope) 
  = ILam pinfo (Just n) (unelab env tm) (unelab ((Lam pinfo tm) :: env) scope)
unelab env (Bind n (Pi Implicit tm) scope) = Implicit
unelab env (Bind n (Pi Explicit tm) scope)
  = IPi Explicit (Just n) (unelab env tm) (unelab ((Pi Explicit tm) :: env) scope)
unelab env (Bind x (PVar y) scope) 
  = IPatvar x (unelab env y) (unelab ((PVar y) :: env) scope)
unelab env (Bind x (PVTy y) scope) = IType
unelab env (App x y) = IApp (unelab env x) (unelab env y)
unelab env TType = IType
unelab env Erased = Implicit

