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

export
repeat : a -> Nat -> List a
repeat _ Z = []
repeat a (S k) = a :: repeat a k

export
nothing : Core (Maybe a)
nothing = pure Nothing

export 
just : a -> Core (Maybe a)
just = pure . Just

export
none : Core (List a)
none = pure []

export 
filterJust : List (Maybe a) -> List a
filterJust [] = []
filterJust (Nothing :: xs) = filterJust xs
filterJust ((Just x) :: xs) = x :: filterJust xs

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

showT : RawImp -> Core ()
showT (IVar x) = log "var"
showT (IPi x y argTy retTy) = do log "pi(" ; showT argTy ; log ")" ; showT retTy
showT (ILam x y argTy scope) = do log "lam(" ; showT argTy ; log ")" ; showT scope
showT (IPatvar x ty scope) = do log "pat(" ; showT ty ; log ")" ; showT scope
showT (IApp x y) = do log "app(" ; showT x ; log ") to (" ; showT y ; log ")"
showT (IHole x) = log "hole"
showT Implicit = log "implicit"
showT IType = log "ty"

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


