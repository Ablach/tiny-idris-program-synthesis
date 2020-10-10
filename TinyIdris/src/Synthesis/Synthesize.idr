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

import Data.List
import Data.List.Quantifiers
import Data.Maybe

data SynthErr : Type where
  NotInContext : (tm : Term vars) -> SynthErr 
  NotAPiBinder : (tm : Term vars) -> SynthErr
  NotWellTyped : (tm : Term vars) -> SynthErr
  NoMatch      : (tm : Term vars) -> SynthErr

getArgs :{vars : _} -> List (Term vars) -> Term vars -> Core (List (Term _),  Term _)

findBest : Term vars -> List (Term vars) -> Term vars
findBest tm tms = ?findBest_rhs

mkClause : Term vars -> List Clause

getReturns : {vars : _} -> Env Term vars -> List (Term vars) -> Term vars -> Maybe (Term vars)

synthClauses : {vars : _} -> 
               {auto c : Ref Ctxt Defs} ->
               Env Term vars -> 
               List (Term vars) -> Term vars -> 
               Core (Either SynthErr (List Clause))
synthClauses env args n
  = do defs <- get Ctxt
       bs <- filterM (convert defs env n) args
       case bs of 
            (x :: xs) => pure $ Right $ mkClause (findBest n (x :: xs))
            [] => do let fs = getReturns env args n 
                     case fs of 
                         Nothing => pure (Left $ NoMatch n)
                         (Just x) => pure (Right $ mkClause x)

export
synthesize_single : {vars : _} ->
                    {auto c : Ref Ctxt Defs} -> 
                    {auto u : Ref UST UState} ->  
                    Env Term vars ->
                    Glued vars -> 
                    Core (Either SynthErr String)
synthesize_single env ty
  =  do t <- getTerm ty
        defs <- get Ctxt
        case t of
         (Bind name (Pi pinfo t') scope) =>
               do (args, tm) <- getArgs [] t
                  case !(nf defs env tm)  of 
                       (NTCon x tag arity xs) => do
                              sc <- synthClauses env args tm -- should actually be a timer fun
                              case sc of 
                                   (Left err) => pure (Left err)
                                   (Right yay) => ?lclausetoStr yay
                       _ => pure (Left $ NotWellTyped t)
         _ => pure (Left $ NotAPiBinder t)
