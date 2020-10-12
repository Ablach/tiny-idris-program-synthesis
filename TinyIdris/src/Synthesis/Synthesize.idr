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
         Core (Either SynthErr (NF vars)) ->
         Core (Either SynthErr Def)

get_args_ret : {vars : _} ->
              {auto c : Ref Ctxt Defs} -> 
              Env Term vars ->
              List (NF vars) ->
              NF vars ->
              Core (List (NF vars) , NF vars)
get_args_ret env l (NBind n (Pi pinfo nml) sc) = 
  do defs <- get Ctxt
     (ls , ret) <- get_args_ret env [] 
                        !(sc defs 
                          (toClosure env 
                            !(quote defs env 
                              !(quote defs env nml))))
     pure $ ((nml :: ls) , ret)
get_args_ret env l nml = pure (l , nml)

isBind : {vars : _} -> (a , NF vars) -> Core Bool
isBind (_ , (NBind _ _ _)) = pure True
isBind _                   = pure False

synthesize : {vars : _} -> 
             {auto c : Ref Ctxt Defs} ->
             Env Term vars -> 
             NF vars -> 
             Core (Either SynthErr (NF vars))
synthesize env tm =
  do defs <- get Ctxt
     qt <- quote defs env tm
     (args , (NTCon n tag arity cs)) <- get_args_ret env [] tm
        | _ => pure (Left $ NotWellTyped qt)  
     
     bs <- traverse (convert defs env (NTCon n tag arity cs)) args
     let zs = zip bs args
     [] <- filterM (\ (x , y) => pure (x == True)) zs
        | ((x, y) :: xs) => pure $ Right y
     
     (x' :: xs') <- filterM isBind zs
        | [] => pure $ Left NoMatch
     
     ps <- traverse (\ (x , y) => get_args_ret env [] y) (x' :: xs')
     ((as, y) :: xs) <- filterM (\ (x , y) => convert defs env (NTCon n tag arity cs) y) ps 
        | [] => pure $ Left $ NoMatch
     
     synthed_args <- traverse (synthesize env) as
     ((l :: ls) , rs) <- pure $ partitionEithers synthed_args
        | ([] , rs) => pure $ Right $ NApp ?head ?rest -- apply y to args
     
     ?fdfs -- repeat for all xs (77) failing if not successful

export
synthesize_single : {vars : _} ->
                    {auto c : Ref Ctxt Defs} -> 
                    {auto u : Ref UST UState} ->  
                    Env Term vars ->
                    RawImp ->
                    Core (Either SynthErr String)
synthesize_single env (IVar x) = 
  do defs <- get Ctxt
     (t , ty) <- checkTerm env (IVar x) Nothing
     nml     <- nf defs env t
     case !(lookupDef x defs) of 
          (Just (MkGlobalDef type None)) => to_str $ to_def env (synthesize env nml)
          (Just (MkGlobalDef type Hole)) => to_str $ to_def env (synthesize env nml)
          (Just (MkGlobalDef type _))    => pure (Left $ AlreadyDefined type)
          Nothing                        => pure (Left $ NotInContext x)
synthesize_single env v = pure (Left $ NotUndefinedVar v)
