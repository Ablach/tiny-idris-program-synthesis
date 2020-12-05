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
import Synthesis.SynthErr
import Synthesis.Unelab
import Synthesis.Resugar

import System
import Data.Strings

showE : {vars : _} -> Env Term vars -> String
showE [] = "[]"
showE ((Lam x z w) :: y) = "lam " ++ show w ++ " :: " ++ showE y
showE ((Pi x z w) :: y) = "pi " ++ show w ++ " :: " ++ showE y
showE ((PVar x z) :: y) = "pvar " ++ show z ++ " :: " ++ showE y
showE ((PVTy x) :: y) = "pvty " ++ show x ++ " :: " ++ showE y

isAuto : String -> Maybe (String)
isAuto s = case (isPrefixOf "auto" s) of 
                True => Just (strSubstr 5 (strLength s) s)
                False => Nothing

runAuto : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} -> 
          String -> Core ()
repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       Core ()

runAuto s = 
  do let Right ttexp = runParser Nothing s (expr "(input)" init)
         | Left err => do coreLift $ printLn err
                          repl 
     case ttexp of 
        (IVar x) => do defs <- get Ctxt
                       Just def <- lookupDef x defs
                        | _ => (do coreLift $ putStrLn "Not in Ctxt" ; repl)
                       let (MetaVar vs env retTy) = definition def
                        | _ => ?dsaad
                       coreLift $ putStrLn $ "retTy = " ++ show retTy
                       coreLift $ putStrLn $ "Env = " ++ showE env
                       repl
        _ => coreLift $ putStrLn $ "Not a hole or var"
     repl

repl = do coreLift $ putStr "> "
          inp <- coreLift getLine
          let Nothing = isAuto inp 
            | Just t => do runAuto t
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

runMain : List ImpDecl -> Core ()
runMain decls
    = do c <- newRef Ctxt !initDefs
         u <- newRef UST initUState
         traverse_ processDecl decls
         repl

main : IO ()
main = do [_, fname] <- getArgs
              | _ => putStrLn "Usage: tinyidris <filename>"
          Right decls <- parseFile fname (do p <- prog fname; eoi; pure p)
              | Left err => printLn err 
          coreRun (runMain decls)
                  (\err => printLn err)
                  pure
