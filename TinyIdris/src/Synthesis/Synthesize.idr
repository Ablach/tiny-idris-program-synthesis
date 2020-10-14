module Synthesis.Synthesize 

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

import TTImp.Elab.Term
import TTImp.TTImp

import Data.List
import Data.List.Quantifiers
import Data.Maybe
import Data.Either

data SynthErr : Type where
  NotInContext    : (tm : Name     ) -> SynthErr 
  NotAPiBinder    : (tm : NF   vars) -> SynthErr
  NotWellTyped    : (tm : Term vars) -> SynthErr 
  NotUndefinedVar : (tm : RawImp   ) -> SynthErr
  AlreadyDefined  : (tm : Term []  ) -> SynthErr
  NoMatch         :                     SynthErr
  Impossible      :                     SynthErr

to_str : Core (Either SynthErr Def) ->
         Core (Either SynthErr String)

to_def : {vars : _} ->
         {auto c : Ref Ctxt Defs} -> 
         Env Term vars ->
         Core (Either SynthErr (Term vars)) ->
         Core (Either SynthErr Def)

synthesize : {vars : _} -> 
             {auto c : Ref Ctxt Defs} ->
             Env Term vars -> 
             Term vars -> 
             Core (Either SynthErr (Term vars))
synthesize env (Ref (TyCon tag arity) n)   =
  do 
     
     ?rest
synthesize env (Bind n (Pi pinfo t) scope) = 
  do let env' = (Lam pinfo t) :: env
     Right rest <- synthesize env' scope
       | Left err => pure $ Left err
     pure $ Right $ Bind n (Lam pinfo t) rest

synthesize env tm = pure $ Left $ NotWellTyped tm



export
synthesize_single : {vars : _} ->
                    {auto c : Ref Ctxt Defs} -> 
                    {auto u : Ref UST UState} ->  
                    Env Term vars ->
                    RawImp ->
                    Core (Either SynthErr String)
synthesize_single env (IVar x) = ?synthesize_single_rhs_1
synthesize_single env (IPi x y argTy retTy) = ?synthesize_single_rhs_2
synthesize_single env (ILam x y argTy scope) = ?synthesize_single_rhs_3
synthesize_single env (IPatvar x ty scope) = ?synthesize_single_rhs_4
synthesize_single env (IApp x y) = ?synthesize_single_rhs_5
synthesize_single env Implicit = ?synthesize_single_rhs_6
synthesize_single env IType = ?synthesize_single_rhs_7
synthesize_single env (IHole s) = ?fjdskf
