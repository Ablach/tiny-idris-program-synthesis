{-
Module: Synthesis.Test
Author: Scott Mora
Last Modified: 28.01.2021
Synthesis: This module provides functionallity 
for testing the program synthesis tool. Outlines 
how to run an individual test, along with running 
multiple. 
-}

module Synthesis.Test

import Synthesis.Synthesise

import Core.Core
import Core.Context
import Core.UnifyState

import System.File
import Data.SortedMap
import Data.Strings
import Data.List

{-
Data types representing an answer sheet and 
functionallity to lookup the answer of a 
given name.
-}
export
Sheet : Type
Sheet = SortedMap String String

export
data Answers : Type where

lookupAnswer : {auto a : Ref Answers Sheet} ->
               String -> Core (Maybe String)
lookupAnswer s = pure $ (SortedMap.lookup s !(get Answers))


{-
Given the name of a test file that is currently loaded, 
locate and parse the answer file. 

Answer files are of the form: 

<name> ! <answer>
-}
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


{-
test: Tests can only be performed on individual
terms, test looks up the definition, if it is 
a metavariable, run the tool and test the 
generating a printout and returning 1 for success or 
0 for a fail. The nat returned will be used when 
running multiple tests.
-}
test : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
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
       let test = ((trim res) == (trim ans))
       let result = if test
                       then "Success"
                       else "Fail"
       log $ "Test: " ++ n ++ " | Result " ++ result ++ 
            " | Expected: " ++ ans ++ " | Actual: " ++ res
       if test then pure 1 else pure 0
test (_,d) = pure 0

{-
testOne: Run an individual test, the number
returned is ignored, since the printout is 
the desired output.
-}
export 
testOne : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} -> 
          {auto a : Ref Answers Sheet} ->
          Name -> Core ()
testOne n = 
  do defs <- get Ctxt
     Just def <- lookupDef n defs
      | _ => log "Name not in context" 
     test (n, def)
     pure ()

{-
runTests: Run multiple tests at once, summing 
the results.
-}
export
runTests : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} -> 
           {auto a : Ref Answers Sheet} ->
           Core ()
runTests = 
 log $ "Total successes " ++ 
       (show $ sum !(traverse id !(mapDefs' test)))
