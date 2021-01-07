module Synthesis.Test

import Synthesis.Synthesize

import Core.Core
import Core.Context
import Core.UnifyState

import System.File
import Data.SortedMap
import Data.Strings
import Data.List


export
Sheet : Type
Sheet = SortedMap String String

export
data Answers : Type where

lookupAnswer : {auto a : Ref Answers Sheet} ->
               String -> Core (Maybe String)
lookupAnswer s = pure $ (SortedMap.lookup s !(get Answers))

export 
getAnswerFile : String -> String
getAnswerFile fname 
  = let (s, s') = break (\ c => c == '.') (drop 15 (unpack fname)) in 
          "Test/AnswerFiles/" ++ (pack s) ++ ".ans"

export
parseAnswers : String -> IO (Either FileError Sheet)
parseAnswers ans = do Right parsed <- readFile ans
                       | Left err => pure $ Left err 
                      pure $ Right $ fromList $ map
                       (\ s => let (a , b) = break (\ c => c == '!') s
                                   b' = pack $ drop 1 (unpack b) in
                               (trim a , trim b'))
                       (lines parsed)

test : {auto c : Ref Ctxt Defs} ->
       {auto a : Ref Answers Sheet} ->
       (Name, GlobalDef) -> Core Nat
test ((UN n),d)
  = do defs <- get Ctxt 
       Just def <- lookupDef (UN n) defs
        | _ => do log "Name not in context" ; pure 0
       let (MetaVar vars env ret) = definition def 
        | _ => pure 0
       Just ans <- lookupAnswer n
        | _ => do log "no answer" ; pure 0
       res <- run (UN n)
       let result = if (res == ans)
                       then "Success"
                       else "Fail"
       log $ "Test: " ++ n ++ " | Result " ++ result ++ 
            " | Expected: " ++ ans ++ " | Actual: " ++ res
       if (res == ans) then pure 1 else pure 0
test (_,d) = pure 0

export
runTests : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} -> 
           {auto a : Ref Answers Sheet} ->
           Core ()
runTests = 
  do newRef Answers !(get Answers)
     let res = sum !(traverse id !(mapDefs' test)) 
     log $ "Total successes " ++ (show res)
     pure ()



