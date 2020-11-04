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

import Data.List
import Data.List.Quantifiers
import Data.Maybe
import Data.Either
import Data.SortedMap

tryUnify : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Env Term vars ->
           List (Term vars) ->
           Term vars -> 
           Core (Either SynthErr (Term vars))
tryUnify env ((Local idx p) :: xs) t 
= do coreLift $ putStrLn $ "unifying " ++ "with " ++ show t
     let bd = getBinder p env
     let b = binderType bd
     coreLift $ putStrLn $ "term inside binder : " ++ show b
     ures <- unify env b t
     case constraints ures of 
       [] => pure (Right (Local idx p))
       (y :: ys) => do ?dsa 
                       tryUnify env xs t
tryUnify env (_ :: xs) t = pure (Left $ Impossible "tryunify _ :: xs")
tryUnify env [] t = pure (Left NoMatch)

synthesize : {vars : _} -> 
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->  
             Env Term vars -> 
             Term vars ->
             Core (Either SynthErr (Term vars))
synthesize env (Ref (TyCon tag arity) n)  
-- rescope our current variables and try and unify any of them 
-- with our type
= do let usable = getUsableEnv [] env 
     tryUnify env usable (Ref (TyCon tag arity) n)  
synthesize env (Bind n (Pi x y z) sc)
-- if we must synthesize a binder then it must be a pi, in which case
-- make a lambda taking in that argument then synthesize the scope
= do coreLift $ putStrLn "Entering binder"
     Right tm <- synthesize ((Lam n y z) :: env) sc
      | Left err  => pure (Left err)
     pure $ Right (Bind n (Lam n y z) tm)
synthesize env (App tf ta) 
{-
 could be an application ie Vect N e is applying N and e to Vect
 synthesize the args, then synth the function, and return an 
 application of the two, this approach won't work, since the 
 thing we get out of the application should be the type? 
 
 the argument is a[2] -- a[2] is a local
 the argument is (add Z m[1]) -- another app
 unifying with Vect -- ref tycon
 term inside binder : (Vect m[1] a[2])

 we should be constructing a term of the final reference, we should
 be getting the values of the local variables and using those as constraints 
 for the synthesis. 


-}
= do coreLift $ putStrLn $ "the argument is " ++ show ta
     Right f <- synthesize env tf
      | Left err => pure (Left err)
     pure (Left NoMatch)
synthesize _ tm 
-- we shouldn't really be given anything else  
-- could possibly be handled nicer
= do case tm of
      (Local idx p) => coreLift $ putStrLn "loc"
      (Ref x y) => coreLift $ putStrLn "ref not tycon"
      (Meta x xs) => coreLift $ putStrLn "meta"
      (Bind x y scope) => coreLift $ putStrLn "bind not pi"
      TType => coreLift $ putStrLn "ty"
      Erased => coreLift $ putStrLn "erased"
      _ => coreLift $ putStrLn "app?"
     coreLift $ putStrLn $ show tm
     pure (Left $ Impossible "synthesize _ tm")

    
export
synthesize_single : {auto c : Ref Ctxt Defs} -> 
                    {auto u : Ref UST UState} ->  
                    Name ->
                    Core (Either SynthErr String)
synthesize_single n = 
-- check if the given name is in the context and a user generated hole
-- if it is try to synthesize otherwise fail  
  do defs <- get Ctxt
     Just def <- lookupDef n defs
      | _ => pure (Left $ NotInContext n)
     (MetaVar vs e retTy)  <- pure $ definition def 
      | _ => pure (Left $ AlreadyDefined $ type def) 
     Right d <- synthesize {vars = vs} e retTy
      | Left err => pure $ Left err 
     pure (Right $ resugar $ unelab e d) 
     

