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
import Synthesis.Monad 

import Data.List
import Data.Maybe
import Data.Either
import Data.SortedMap

printResult : Search String -> String

data UFail : Type where

tryUnify : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           Env Term vars ->
           Term vars -> Term vars -> 
           Core (Search (SortedMap Int Constraint))
tryUnify env a b
  = do u <- newRef UST initUState
       newRef UFail False 
       res <- catch (unify env a b) 
                    (\ _ => do put UFail True 
                               pure $ MkUnifyResult [] False)
       if !(get UFail) 
          then pure $ Go (constraints !(get UST)) 
          else pure Stop

checkLocals : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              (env : Env Term vars) -> 
              (usable : List (Term vars)) -> 
              (tm : Term vars) ->
              Core (List (Search (Term vars)))
checkLocals env ((Local idx p) :: xs) tm 
  = case !(tryUnify env tm (binderType $ getBinder p env)) of
         Stop => checkLocals env xs tm
         (Go x) => pure $ (Go (Local idx p)) :: !(checkLocals env xs tm) 
checkLocals env (_ :: xs) tm = checkLocals env xs tm
checkLocals _ [] _ = pure []

searchFunctions : {vars : _} ->
                  (env : Env Term vars) ->
                  (tm : Term vars) ->
                  Core (List (Search (Term vars)))
searchFunctions env tm = ?searchFunctions_rhs

tryConstructor : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 (env : Env Term vars) ->
                 (tm : Term vars) ->
                 (con : Name) ->
                 Core (List (Search (Term vars)))
tryConstructor env tm n
  = do Just def <- lookupDef n !(get Ctxt)
        | _ => pure []
       case definition def of
            (DCon tag arity ty) => 
               ?fsdd_3
               {-
                  for each arg genreate metas, then attempt unification, 
                  if it fails, fail, if it returns with constraints, 
                  attempt to synthesise the terms using the constraints.
              -}
            (TCon tag arity datacons) => 
              pure $ concat !(traverse (tryConstructor env tm) datacons)         
            _ => pure []
      
 {-    
Search is just maybe, could possibly take in a core a and wrap it, would
need wrappers for definition and lookup, might not be worth it though,
could lead to issues with core. 
-}

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
       datas <- case ret of 
                  (Ref (TyCon tag arity) n) 
                    => tryConstructor env tm n
                  _ => pure []
       recurse <- searchFunctions env tm
       pure $ locals ++ datas ++ recurse

run : {auto c : Ref Ctxt Defs} ->
      Name -> Core String
run n = do Just def <- lookupDef n !(get Ctxt)
            | _ => pure "Invalid Name" 
           let (MetaVar vars env retTy) = definition def
            | _ => pure "Invalid Name"
           results <- synthesiseTerm {vars = vars} env retTy
           ?fsfs      
