module Synthesis.Synthesize 

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState

import TTImp.Elab.Term

export
synthesize_single : {vars : _} ->
                    {auto c : Ref Ctxt Defs} -> 
                    {auto u : Ref UST UState} ->  
                    Env Term vars ->
                    Glued vars -> 
                    Core String
synthesize_single env ty =
  case !(getTerm ty) of 
      (Bind name tm scope) => do defs <- get Ctxt
                                 let env' : Env Term (name :: vars)
                                     env' = tm :: env
                                 let gscope : Glued (name :: vars) 
                                     gscope = gnf env' scope
                                 synthesize_single env' gscope                        
      (Ref namety n) => ?do_synthesizey_things
      otherwise => pure "Not a function type"
