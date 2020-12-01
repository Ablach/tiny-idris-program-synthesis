module Synthesis.Synthesize 

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Unify
import Core.UnifyState
import Core.Value

import TTImp.Elab.Term
import TTImp.TTImp

import Synthesis.Rescope
import Synthesis.Unelab
import Synthesis.Resugar
import Synthesis.SynthErr
import Synthesis.Monad as SM

import Data.List
import Data.Maybe
import Data.Either
import Data.SortedMap

synthesise : {vars : _} -> 
             {auto c : Ref Ctxt Defs} ->
             Env Term vars -> 
             Name -> 
             Core (Search (Term vars))

searchLocals : {vars : _} -> Env Term vars -> Search (Term vars) -> List (Search (Term vars))

searchFunctions : {vars : _} -> Env Term vars -> Search (Term vars) -> List (Search (Term vars))

attemptDatacons : {vars : _} -> Env Term vars -> Search (Term vars) -> List (Search (Term vars))

tryRec : {vars : _} -> Env Term vars -> Search (Term vars) -> List (Search (Term vars))

getBest : {vars : _} -> List (Search (Term vars)) -> Search (Term vars)

enumerateEnv : {vars : _} -> 
             {auto c : Ref Ctxt Defs} ->
             Env Term vars -> 
             Search (Term vars) ->
             List (Search (Term vars))
enumerateEnv env tm
  = getFounds $
    (searchLocals env tm)    ++
    (attemptDatacons env tm) ++
    (searchFunctions env tm) ++
    (tryRec env tm)

synthesiseTerm : {vars : _ } -> {auto c : Ref Ctxt Defs} ->
                 Env Term vars -> Term vars -> Search (Term vars)


run : {auto c : Ref Ctxt Defs} ->
      Name -> Core String
run n = do
 defs <- get Ctxt 
 Just d <- lookupDef n defs 
  | _ => pure "Invalid name"
 let f = definition d
 ?fsd

