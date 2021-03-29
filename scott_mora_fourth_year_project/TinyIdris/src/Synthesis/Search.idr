{-
Module: Synthesis.Search 
Author: Scott Mora
Last Modified: 23.03.2021
Summary: A Record wrapping up the information
to perform program synthesis on an individual 
term.
-}

module Synthesis.Search 

import Core.TT
import Core.Env
import TTImp.TTImp

public export
record Search (vars : List Name) where
 constructor MkSearch
 depth : Nat
 name : Name
 env : Env Term vars
 lhs : RawImp
 target : Term vars 


