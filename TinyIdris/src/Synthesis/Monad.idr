module Synthesis.Monad 

import Core.Core
import Core.TT
import Core.Env
import Core.UnifyState
import Synthesis.SynthErr

public export
data Search : Type -> Type where
  Stop : Search a
  Go   : a -> Search a


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

