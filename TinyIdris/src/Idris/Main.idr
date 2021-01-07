module Idris.Main 
import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

import TTImp.Elab.Term

import TTImp.Parser
import TTImp.ProcessDecl
import TTImp.TTImp

import Parser.Source

import Synthesis.Synthesize
import Synthesis.Unelab
import Synthesis.Resugar
import Synthesis.Monad
import Synthesis.Test

import System
import System.File
import Data.Strings
import Data.List
import Data.SortedMap


isAuto : String -> Maybe (String)
isAuto s = case (isPrefixOf "auto" s) of 
                True => Just (strSubstr 5 (strLength s) s)
                False => Nothing

isTest : String -> Bool
isTest s = isPrefixOf "test" s 

runAuto : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} -> 
          {auto a : Ref Answers Sheet} ->
          String -> Core ()

repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       {auto a : Ref Answers Sheet} ->
       Core ()

runAuto s = 
  do let Right ttexp = runParser Nothing s (expr "(input)" init)
         | Left err => do coreLift $ printLn err
                          repl 
     case ttexp of 
        (IVar x) => coreLift $ putStrLn $ !(run x) 
        _ => coreLift $ putStrLn $ "Not a hole or var"
     repl
     
repl = do coreLift $ putStr "> "
          inp <- coreLift getLine
          let Nothing = isAuto inp 
            | Just t => do coreLift $ putStrLn "Running Auto Search: "
                           runAuto t
                           repl
          let False = isTest inp 
            | True => do coreLift $ putStrLn "Running tests: "
                         runTests
                         repl
          let Right ttexp = runParser Nothing inp (expr "(input)" init)
              | Left err => do coreLift $ printLn err
                               repl
          (tm, ty) <- checkTerm [] ttexp Nothing
          coreLift $ putStrLn $ "Checked: " ++ show tm
          defs <- get Ctxt
          coreLift $ putStrLn $ "Type: " ++ show !(normalise defs [] !(getTerm ty))
          nf <- normalise defs [] tm
          coreLift $ putStrLn $ "Evaluated: " ++ show nf
          -- coreLift $ putStrLn $ "resugared: " ++ resugar (unelab [] tm)
          repl

runMain : List ImpDecl -> Sheet -> Core ()
runMain decls ans
    = do c <- newRef Ctxt !initDefs
         u <- newRef UST initUState
         a <- newRef Answers ans
         traverse_ processDecl decls
         repl

main : IO ()
main = do [_, fname] <- getArgs
              | _ => putStrLn "Usage: tinyidris <filename>"
          Right decls <- parseFile fname (do p <- prog fname; eoi; pure p)
              | Left err => printLn err  
          Right answers <- parseAnswers (getAnswerFile fname)
              | Left err => printLn (getAnswerFile fname)
          coreRun (runMain decls answers)
                  (\err => printLn err)
                  pure
