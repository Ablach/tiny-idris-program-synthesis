{-This file contains modifications by Scott Mora on line 26-}

module TTImp.ProcessType


import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState

import TTImp.Elab.Term
import TTImp.TTImp

-- Add a name and type, with no definition, to the context.
-- Idris 2 has to work a little bit harder, to deal with namespaces, and
-- defining names in an outer environment (e.g. where blocks) but otherwise
-- this just checks the type and update the context.
export
processType : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Name -> RawImp -> Core ()
processType n ty
    = do (tychk, _) <- checkTerm [] ty (Just gType)
         -- Exercise: We should also check whether it's already defined!
         addFunction n tychk
         addDef n (newDef tychk None)
         coreLift $ putStrLn $ "processed type " ++ (show n)
