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

record Search where
  constructor mkSearch
  topLevel : Term vars
  depth : Nat 

data UnifyFail : Type where

result : {vars : _} -> List (Term vars) -> Maybe (Term vars)
result [] = Nothing
result (x :: xs) = Just x


showCs : List Int -> SortedMap Int Constraint -> Core ()
showCs [] x = coreLift $ putStrLn "No more constraints"
showCs (y :: xs) x 
= do let c = lookup y x
     case c of 
        Nothing => coreLift $ putStrLn ""
        (Just (MkConstraint env z w)) =>
           coreLift $ putStrLn $ "constraint " ++ show z ++ " = " ++ show w
        (Just (MkSeqConstraint env ys zs)) => coreLift $ putStrLn "seq con"
        (Just Resolved) => coreLift $ putStrLn "resolved"
     showCs xs x

tryUnify : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           {auto o : Ref UnifyFail Bool} ->
           Env Term vars ->
           List (Term vars) ->
           Term vars -> 
           Core (Either SynthErr (List (Term vars)))
tryUnify env ((Local idx p) :: xs) t 
= do coreLift $ putStrLn $ "unifying " ++ "with " ++ show t
     let bd = getBinder p env
     let b = binderType bd
     coreLift $ putStrLn $ "term inside binder : " ++ show b
     ures <- catch (unify env b t) (\ err => do put UnifyFail True
                                                pure $ MkUnifyResult [] False)
     False <- get UnifyFail
      | _ => do put UnifyFail False ; coreLift $ putStrLn "Unification failed" ; tryUnify env xs t
     case constraints ures of 
      [] => do Right rest <- tryUnify env xs t
                 | _ => pure (Right [Local idx p])
               pure (Right $ [Local idx p] ++ rest)  
         
      (y :: ys) => do ust <- get UST
                      let cs = constraints ust
                      showCs (y :: ys) cs
                      tryUnify env xs t

tryUnify env (_ :: xs) t = pure (Left $ Impossible "tryunify _ :: xs")
tryUnify env [] t = pure (Left NoMatch)

synthesize : {vars : _} -> 
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->  
             {auto o : Ref UnifyFail Bool} ->
             Nat ->
             Env Term vars -> 
             Term vars ->
             Core (Either SynthErr (List (Term vars)))

synthesize d env (Ref (TyCon tag arity) n)  
-- rescope our current variables and try and unify any of them 
-- with our type
= do let usable = getUsableEnv [] env 
     tryUnify env usable (Ref (TyCon tag arity) n)  

synthesize d env (Bind n (Pi x y z) sc)
-- if we must synthesize a binder then it must be a pi, in which case
-- make a lambda taking in that argument then synthesize the scope
= do coreLift $ putStrLn "Entering binder"
     Right ts <- synthesize d ((Lam n y z) :: env) sc
      | Left err  => pure (Left err)
     pure $ Right $ map (\ tm => (Bind n (Lam n y z) tm)) ts

synthesize d env (App tf ta) 
{-
 could be an application ie Vect N e is applying N and e to Vect
 synthesize the args, then synth the function, and return an 
 application of the two, this approach won't work, since the 
 thing we get out of the application should be the type? 

 we should be constructing a term of the final reference, we should
 be getting the values of the local variables and using those as constraints 
 for the synthesis. 
-}
= do let ((Ref (TyCon _ _) n) , args) = getFnArgs (App tf ta)
      | _ => pure (Left $ Impossible "Synthesize Application return of getFnArgs")
     let usable = getUsableEnv [] env 
     coreLift $ putStrLn "-----------------"
     coreLift $ putStrLn $ "The type is " ++ show n
     coreLift $ putStrLn $ "The args are " ++ concat (intersperse " " (map show args))
     coreLift $ putStrLn "-----------------"
     Left _ <- tryUnify env usable (App tf ta)
      | Right ts => pure $ Right ts
     -- now that we've failed to simply pick something from the local env we need to start
     -- thinking, look at the data constructors and see first if we can synthesize them
     defs <- get Ctxt
     Just def <- lookupDef n defs
      | _ => pure (Left $ Impossible "Synthesize Application no definition")
     let (TCon _ _ datacons) = definition def
      | _ => pure (Left $ Impossible "Synthesize Application not tcon")
     ?fin

synthesize _ _ tm 
-- we shouldn't really be given anything else  
-- could possibly be handled nicer
= do case tm of
      (Local idx p) => coreLift $ putStrLn "loc"
      (Ref x y) => coreLift $ putStrLn "ref not tycon"
      (Meta x xs) => coreLift $ putStrLn "meta"
      (Bind x y scope) => coreLift $ putStrLn "bind not pi"
      TType => coreLift $ putStrLn "ty"
      Erased => coreLift $ putStrLn "erased"
      _ => coreLift $ putStrLn "app"
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
     let (MetaVar vs e retTy) = definition def 
      | _ => pure (Left $ AlreadyDefined $ type def) 
     o <- newRef UnifyFail False
     Right d <- synthesize {vars = vs} 10 e retTy
      | Left err => pure $ Left err 
     let Just t = result d
      | Nothing => pure $ Left NoMatch
     pure (Right $ resugar $ unelab e t)
     

