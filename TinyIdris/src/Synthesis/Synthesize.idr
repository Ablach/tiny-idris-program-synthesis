module Synthesis.Synthesize 

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState

import TTImp.Elab.Term

export
synthesize_single : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} -> 
                    (Term [], Glued []) -> 
                    Core String
synthesize_single (tm , ty) =
  case !(getTerm ty) of -- replacing with tm does? change name maybe
      (Bind arg rest scope) => ?dfs
      otherwise => pure "Not a function type"
