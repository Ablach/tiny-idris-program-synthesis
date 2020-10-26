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

import System
import Data.Strings

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
     (tm , ty) <- checkTerm [] ttexp Nothing 
     defs <- get Ctxt
     coreLift $ putStrLn $ "Normalised type " ++ show !(normalise defs [] !(getTerm ty))
     case ttexp of 
        (IVar x) =>
          do coreLift $ putStrLn "IVar"
             Just d <- lookupDef x defs 
              | _ => coreLift $ putStrLn "Not in context!"
             case definition d of 
                  None => coreLift $ putStrLn "none"
                  (PMDef args treeCT) => coreLift $ putStrLn "pm def"
                  (DCon tag arity) => coreLift $ putStrLn "dcon"
                  (TCon tag arity datacons) => coreLift $ putStrLn "tcon"
                  Hole => coreLift $ putStrLn "hole"
                  (Guess guess constraints) => coreLift $ putStrLn "guess!"
                  (MetaVar vs e ret args) =>
                   do coreLift $ putStrLn "metavar"
                      case ret of 
                           (Local idx p) => coreLift $ putStrLn "ret = local"
                           (Ref y z) => coreLift $ putStrLn "ret = ref"
                           (Meta y xs) => coreLift $ putStrLn "ret = meta"
                           (Bind y z scope) => coreLift $ putStrLn "ref = bind"
                           (App y z) => coreLift $ putStrLn "ref = app"
                           TType => coreLift $ putStrLn "ref = type"
                           Erased => coreLift $ putStrLn "ref = erased"
             case type d of
                  (Local idx p) => coreLift $ putStrLn "local"
                  (Ref y z) => coreLift $ putStrLn "ref"
                  (Meta y xs) => coreLift $ putStrLn "meta"
                  (Bind y z scope) => coreLift $ putStrLn "bind"     
                  (App y z) => coreLift $ putStrLn "app"
                  TType => coreLift $ putStrLn "type"    
                  Erased => coreLift $ putStrLn "erased"
        (IHole x) => 
          do coreLift $ putStrLn "IVar"
             Just d <- lookupDef x defs 
              | _ => coreLift $ putStrLn "Not in context!"
             case definition d of 
                  None => coreLift $ putStrLn "none"
                  (PMDef args treeCT) => coreLift $ putStrLn "pm def"
                  (DCon tag arity) => coreLift $ putStrLn "dcon"
                  (TCon tag arity datacons) => coreLift $ putStrLn "tcon"
                  Hole => coreLift $ putStrLn "hole"
                  (Guess guess constraints) => coreLift $ putStrLn "guess!"
                  (MetaVar vs e ret args) =>
                   do coreLift $ putStrLn "metavar"
                      case ret of 
                           (Local idx p) => coreLift $ putStrLn "ret = local"
                           (Ref y z) => coreLift $ putStrLn "ret = ref"
                           (Meta y xs) => coreLift $ putStrLn "ret = meta"
                           (Bind y z scope) => coreLift $ putStrLn "ref = bind"
                           (App y z) => coreLift $ putStrLn "ref = app"
                           TType => coreLift $ putStrLn "ref = type"
                           Erased => coreLift $ putStrLn "ref = erased"
             case type d of
                  (Local idx p) => coreLift $ putStrLn "local"
                  (Ref y z) => coreLift $ putStrLn "ref"
                  (Meta y xs) => coreLift $ putStrLn "meta"
                  (Bind y z scope) => coreLift $ putStrLn "bind"     
                  (App y z) => coreLift $ putStrLn "app"
                  TType => coreLift $ putStrLn "type"    
                  Erased => coreLift $ putStrLn "erased"

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
          putStrLn $ concat $ map show decls
          coreRun (runMain decls)
                  (\err => printLn err)
                  pure
