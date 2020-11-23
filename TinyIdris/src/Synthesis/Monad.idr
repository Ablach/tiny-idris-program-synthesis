module Synthesis.Monad 

import Core.TT
import Core.Env
import Core.UnifyState
import Synthesis.SynthErr

data Search : Type -> Type where 
  Result : Search a
  More   : a -> (Search a) -> Search a

mutual 
Functor Search where
  map f Result = Result
  map f (More x y) = More (f x) (map f y)

Monad Search where
  Result >>= f = Result
  (More x y) >>= f = do x' <- f x
                        More x' ?sfd

Applicative Search where
  a <*> b = ?ffd

{-
data Synth : Type -> Type where
  Failure : Synth SynthErr
  Refined : Synth Search -> Synth Search 
  Unifiable : Search -> Synth (Term vars)
map func x = ?map_rhs

Functor Synth where
  map f Failure = Failure ?das
  map f (Refined x) = ?fsd_2
  map f (Unifiable x) = ?fsd_3
  -}    
{-
data Synth : Type -> Type where
  Success : a -> Synth (a , List Constraint)
  Failure : a -> Synth (a , SynthErr)

Functor Synth where
  map f (Success x) = ?dsa
  map f (Failure x) = ?sdsa 
-}
{-


record Search where
  constructor MkSearch
  vars     : List Name
  depth    : Nat
  target   : Term vars
  env      : Env Term vars
  guesses  : List (Term vars , List Constraint)

data SynthState = Start | Ongoing Search | Finish (Term vars) | Failure SynthErr
data Continue = Yes | No

data Act :  (ty : Type) -> SynthState -> (ty -> SynthState) -> Type where
  Init    : (tm : Term vars) -> (env : Env Term vars) ->
            Act ()
            Start 
            (const (Ongoing (MkSearch vars 10 tm env [])))
  Collect : 
            Act (List (Term vars , List Constraint))
            (Ongoing (MkSearch vars d t e []))
            (\ result => case result of
                          [] => Failure (NoMatch)
                          xs => Ongoing (MkSearch vars d t e xs)) 
  Refine  : Act Continue 
            (Ongoing a) 
            (\ synRes => case synRes of
                          Yes => ?dsa_1 
                          No  => ?dsa_2)
  Timeout : Act () -- we would need some seperate state for failure
            (Ongoing (MkSearch vars 0 tm env))
            ()
  Fail    : (s : SynthErr) -> 
            Act ()
            (Ongoing a)
            (const (Failure s))
  Return  : Act ()
            (Ongoing (MkSearch v d tm e ((t , []) :: ts)))
            (const (Finish t))
-}

