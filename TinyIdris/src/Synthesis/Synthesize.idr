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

synthesize : {vars : _} -> 
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Env Term vars ->
             NameType -> Name -> Maybe ImpDecl
synthesize env namety name = ?synthesize_rhs


to_string : ImpDecl -> String

export
synthesize_single : {vars : _} ->
                    {auto c : Ref Ctxt Defs} -> 
                    {auto u : Ref UST UState} ->  
                    Env Term vars ->
                    Glued vars -> 
                    Core String
synthesize_single env ty =
  do t <- getTerm ty 
     case t of 
      (Bind name tm scope) => do defs <- get Ctxt
                                 let env' : Env Term (name :: vars)
                                     env' = tm :: env
                                 let gscope : Glued (name :: vars) 
                                     gscope = gnf env' scope
                                 synthesize_single env' gscope                        
      (Ref namety n) => case synthesize env namety n of 
                             Nothing => pure "Could not synthesize a definiton."
                             (Just x) => pure $ to_string x
      otherwise => pure "Not a function type"
