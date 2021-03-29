{-
Module: Synthesis.Util
Author: Scott Mora
Last Modified: 21.03.2021
Summary: Provides various utitlity 
functions used within searching and 
case splitting. 
-}

module Synthesis.Util

import Core.Core
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

import Synthesis.Resugar

{-
The following three definitions 
exist purely to clean up the codebase.
-}
export
nothing : Core (Maybe a)
nothing = pure Nothing

export 
just : a -> Core (Maybe a)
just = pure . Just

export
none : Core (List a)
none = pure []

{-
The following two datatypes are used
for handling exceptions within the 
remaining functions. 
-}

data UFail : Type where
data EFail : Type where


{-
tryUnify: Attempt unification between 
two terms, if unification throws an 
exception handle it, returning nothing, 
otherwise return the result. 
-}
export
tryUnify : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           Env Term vars ->
           Term vars -> Term vars -> 
           Core (Maybe (UnifyResult))
tryUnify env a b
  = do 
       newRef UFail False 
       ures <- catch (unify env a b) 
                     (\_ => do put UFail True 
                               pure $ MkUnifyResult [] False)
       if !(get UFail) 
          then nothing 
          else pure $ Just (ures)


{-
filterCheckable: Attempt to type check a list of terms, 
returning only those for which type checking succeeds.
-}
export
filterCheckable : {auto c : Ref Ctxt Defs} -> 
                  {auto u : Ref UST UState} ->
                  List (RawImp, List Name) ->
                  Core (List (Term [], Glued [], RawImp, List Name))
filterCheckable [] = pure []
filterCheckable ((x, b) :: xs) =
  do newRef EFail False
     (tm, gd) <- catch (checkTerm [] x Nothing) 
                       (\ _ => do put EFail True
                                  pure (Erased, MkGlue (pure Erased)
                                                       (\_ => pure NErased)))
     if !(get EFail)
        then filterCheckable xs
        else pure ((tm, gd, x, b) :: !(filterCheckable xs))

                 
{-
fillMetas: Given a value and a name, if the value is
a binder that accepts arguments, generate a metavariable 
for the argument and proceed to the end of the term, returning
the result, and the list of metavariables generated. 

Should be used with data constructors.

Nil: a -> Vec Z a becomes (Vec Z a, a)
-} 
export
fillMetas : {vars : _} -> 
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Env Term vars -> NF vars ->
            Core (NF vars , List (Term vars, Name))
fillMetas env (NBind n (Pi n' pinfo tm) scope) 
  = do defs <- get Ctxt 
       nm <- genName "filling"
       mta <- newMeta env nm !(quote defs env tm) Hole
       (f , args) <- fillMetas env !(scope defs (toClosure env mta))
       pure (f , (mta , nm) :: args)
fillMetas env tm = pure (tm , [])


