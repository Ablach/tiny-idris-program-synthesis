module Synthesis.Search 

import Core.TT
import Core.Env
import TTImp.TTImp

public export
-- Exists purely to clean up type signatures
record Search (vars : List Name) where
 constructor MkSearch
 depth : Nat
 name : Name
 env : Env Term vars
 lhs : RawImp
 target : Term vars 


