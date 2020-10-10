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

rest :  {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} -> 
        RawImp -> Core ()
rest ttexp = do (tm, ty) <- (checkTerm [] ttexp Nothing)
                defs <- get Ctxt
                coreLift $ putStrLn $ "show term: " ++ show tm 
                coreLift $ putStrLn $ "show get term of glued: " ++ show !(getTerm ty)
                coreLift $ putStrLn $ "show normalised get term of glued: " ++ show !(normalise defs [] !(getTerm ty))
               -- coreLift $ putStrLn $ "show get nf of glued: " ++ show !(getNF ty)
               -- coreLift $ putStrLn !(synthesize_single [] ty)
                 

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
          (IVar x) => do coreLift $ putStrLn "I am a var"
                         defs <- get Ctxt
                         t <- lookupDef x defs
                         case t of
                              Nothing => rest ttexp 
                              (Just y) => do
                                        let tpe = type y
                                        coreLift $ putStrLn $ "lookup " ++ show tpe
                                        rest ttexp
          (IPi x y argTy retTy) => do coreLift $ putStrLn "I am a pi"
                                      rest ttexp
          (ILam x y argTy scope) => do coreLift $ putStrLn "I am a lam" 
                                       rest ttexp
          (IPatvar x ty scope) =>  do coreLift $ putStrLn "I am a pat" 
                                      rest ttexp
          (IApp x y) => do coreLift $ putStrLn "I am a app" 
                           rest ttexp
          Implicit => do coreLift $ putStrLn "I am a imp" 
                         rest ttexp
          IType => do coreLift $ putStrLn "I am a type" 
                      rest ttexp


{-
runAuto s = 
  do let Right ttexp = runParser Nothing s (expr "(input)" init)
         | Left err => do coreLift $ printLn err
                          repl 
     case ttexp of 
        IVar name => do defs <- get Ctxt
                        Just d <- lookupDef name defs
                          | Nothing => do coreLift $ putStrLn "Provided name not in context."
                                          repl
                        case definition d of  
                          None => do (tm , glued)<- checkTerm [] ttexp Nothing
                                     res <- synthesize_single [] glued
                                     coreLift $ putStrLn res
                                     repl
                          Hole => do (tm , glued) <- checkTerm [] ttexp Nothing
                                     res <- synthesize_single [] glued
                                     coreLift $ putStrLn res
                                     repl
                          otherwise => do coreLift $ putStrLn "Definition exists; nothing to do"
                                          repl
        otherwise => do coreLift $ putStrLn "Expression is not a name." 
                        repl     
                        -}
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
          coreRun (runMain decls)
                  (\err => printLn err)
                  pure
