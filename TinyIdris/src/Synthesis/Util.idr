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

export
repeat : a -> Nat -> List a
repeat _ Z = []
repeat a (S k) = a :: repeat a k

export
nothing : Core (Maybe a)
nothing = pure Nothing

export
none : Core (List a)
none = pure []

data UFail : Type where
data EFail : Type where
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

export
filterCheckable : {auto c : Ref Ctxt Defs} -> 
                  {auto u : Ref UST UState} ->
                  List (RawImp, b) -> Core (List (Term [], Glued [], RawImp, b))
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


