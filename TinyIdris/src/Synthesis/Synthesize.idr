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

printResult : Search String -> String

tryUnify : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           Env Term vars ->
           Term vars -> Term vars -> 
           Core (Search (Term vars))
tryUnify env a b
  = do u <- newRef UST ?fds
       res <- catch (unify env a b) ?dfas
       ?sfsf


checkLocals : {vars : _} ->
              (env : Env Term vars) -> 
              (usable : List (Term vars)) -> 
              (tm : Term vars) ->
              Core (List (Search (Term vars)))
checkLocals env [] tm = pure []
checkLocals env ((Local idx p) :: xs) tm = ?ewqe_1 
checkLocals env _ tm = ?ewqe_7

searchFunctions : {vars : _} ->
                  (env : Env Term vars) ->
                  (tm : Term vars) ->
                  Core (List (Search (Term vars)))
searchFunctions env tm = ?searchFunctions_rhs

tryConstructors : {vars : _} ->
                  (env : Env Term vars) ->
                  (tm : Term vars) ->
                  (base : Term vars) ->
                  Core (List (Search (Term vars)))
tryConstructors env tm base = ?tryConstructors_rhs

synthesiseTerm : {vars : _ } ->
                 {auto c : Ref Ctxt Defs} ->
                 Env Term vars ->
                 Term vars -> 
                 Core (List (Search (Term vars)))
synthesiseTerm env (Bind n (Pi nm pinfo tm) scope) 
  = do let env' : Env Term (n :: _) = (Lam nm pinfo tm) :: env
       results <- synthesiseTerm env' scope
       pure $ map (\ res =>
                      map (\ tm' =>
                             (Bind n (Lam nm pinfo tm) tm'))
                             res) results
synthesiseTerm env tm
  = do let (ret , args) = getFnArgs tm
       -- when we get usable, we check for lambdas and patterns 
       -- returning locals
       locals <- checkLocals env (getUsableEnv [] env) tm
       datas <- tryConstructors env tm ret
       recurse <- searchFunctions env tm
       pure $ locals ++ datas ++ recurse

run : {auto c : Ref Ctxt Defs} ->
      Name -> Core String
run n = do defs <- get Ctxt
           Just def <- lookupDef n defs 
            | _ => pure "Invalid Name" 
           let (MetaVar vars env retTy) = definition def
            | _ => pure "Invalid Name"
           results <- synthesiseTerm {vars = vars} env retTy
           ?fsfs      
