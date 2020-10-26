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

import Synthesis.Unelab
import Synthesis.Resugar

import Data.List
import Data.List.Quantifiers
import Data.Maybe
import Data.Either

data SynthErr : Type where
  NotInContext    : (tm : Name     ) -> SynthErr 
  NotAPiBinder    : (tm : NF   vars) -> SynthErr
  NotWellTyped    : (tm : Term vars) -> SynthErr 
  NotHole         : (tm : RawImp   ) -> SynthErr
  AlreadyDefined  : (tm : Term []  ) -> SynthErr
  NoMatch         :                     SynthErr
  Impossible      :                     SynthErr

synthesize : {vars : _} -> 
             {auto c : Ref Ctxt Defs} ->
             Env Term vars -> 
             Term vars -> List (Term vars) -> 
             Core (Either SynthErr (Term vars))
synthesize env (Ref (TyCon tag arity) n) args 
  = do Just (MkIsDefined prf) <- pure $ defined n env
         | _ => pure (Left NoMatch)
       Lam pinfo tm <- pure $ getBinder prf env
        | _ => pure (Left Impossible)
       pure (Right tm)
synthesize _ _ _ = pure (Left Impossible) -- hopefully

export
synthesize_single : {auto c : Ref Ctxt Defs} -> 
                    {auto u : Ref UST UState} ->  
                    RawImp ->
                    Core (Either SynthErr String)
synthesize_single (IVar n) = 
  do defs <- get Ctxt
     Just def <- lookupDef n defs
      | _ => pure (Left $ NotInContext n)
     (MetaVar vs e retTy args)  <- pure $ definition def 
      | _ => pure (Left $ AlreadyDefined $ type def)
     Right d <- synthesize {vars = vs} e retTy args
      | Left err => pure $ Left err 
     pure (Right $ resugar $ unelab e d) 
     
synthesize_single tm = pure (Left $ NotHole tm)
