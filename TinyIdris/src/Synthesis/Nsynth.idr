import Core.TT
import Core.Context
import Core.Core
import Core.Value
import Core.Env 
import Core.Normalise
import Synthesis.Monad
import Data.List

synthesise : {vars : _} ->
             {auto c : Ref Ctxt Defs} -> 
             Env Term vars -> NF vars -> 
             Core (Search (NF vars))

synthesise env (NBind n (Pi n' pinfo tm) scope) 
  = do defs <- get Ctxt
       synthesise env !(scope defs ?gfd)
       ?ff_8
synthesise env (NApp f as) = ?ff_2
synthesise env (NDCon n tag arity as) = ?ff_3
synthesise env (NTCon n tag arity ds) = ?ff_4
synthesise env _ = pure Stop

run : {auto c : Ref Ctxt Defs} -> 
      Name -> Core String
run n = do defs <- get Ctxt
           Just def <- lookupDef n defs
            | _ => pure "Invalid name"
           let (MetaVar vars env retTy) = definition def
            | _ => pure "Invalid name"
           --tm <-synthesise env 
           -- !(nf defs env (rewrite sym (appendNilRightNeutral vars) in weakenNs vars (type def)))
           ?fsfs
