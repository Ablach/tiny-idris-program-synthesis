module Synthesis.Monad 

import Core.Core
import Core.TT
import Core.Env
import Core.UnifyState


public export
data Search : Type -> Type where
  Stop : Search a
  Go   : a -> Search a -- : Core a -> Search a
  -- Choose : Core (F a) -> Search a

mutual 
  public export
  Functor Search where
    map f Stop = Stop
    map f (Go x) = Go (f x)

  public export 
  Applicative Search where
    pure  a = Go a 
    (Go f) <*> a = map f a
    _ <*> _ = Stop

  public export 
  Monad Search where
    Stop >>= k = Stop
    (Go x) >>= k = case k x of
                       Stop => Stop
                       (Go z) => Go z
export
Show a => Show (Search a) where
  show Stop = "Stop"
  show (Go x) = show x

public export
stop : Core (Search a)
stop = pure Stop

public export 
none : Core (List a)
none = pure []

public export
travS : (a -> Core a) -> Search a -> Core (Search a)
travS f Stop = pure Stop
travS f (Go x) = pure $ Go !(f x)
