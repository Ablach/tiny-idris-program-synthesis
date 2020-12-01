module Synthesis.Monad 

import Core.Core
import Core.TT
import Core.Env
import Core.UnifyState
import Synthesis.SynthErr

union : List Constraint -> List Constraint -> Maybe (List Constraint)

public export
data Search : Type -> Type where 
  -- a depth, a list of constraints, what to do next
  Searching : a -> (n : Nat) -> (cs : List Constraint) -> Search a
  -- the thing we've found
  Found : (tm : Term vars) -> Search a
  Stopped : Search a

mutual 
  public export 
  Functor Search where
    map f (Searching x n cs) = Searching  (f x) n cs
    map f (Found tm) = Found tm
    map f Stopped = Stopped

  public export
  Applicative Search where
    pure a = Searching a 10 [] 
    (Searching f n' cs') <*> (Searching x n cs) 
      = Searching (f x) n cs 
    (Searching f n cs) <*> (Found tm) = Found tm
    _ <*> _ = Stopped

  public export
  Monad Search where
    (Searching x n cs) >>= p 
      = case p x of 
         (Searching x' n' cs') => 
            case union cs cs' of
                 Nothing => Stopped 
                 (Just cs'') => Searching x' n' cs''
         b => b
    (Found tm) >>= k = Found tm
    Stopped >>= k = Stopped
    
public export 
getFounds : List (Search a) -> List (Search a)
getFounds [] = []
getFounds ((Found tm) :: xs) = Found tm :: getFounds xs
getFounds (_ :: xs) = getFounds xs
