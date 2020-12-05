module Synthesis.Monad 

import Core.Core
import Core.TT
import Core.Env
import Core.UnifyState
import Synthesis.SynthErr

public export
data Search : Type -> Type where
  Stop : Search a
  Go   : a -> Search a -> Search a


mutual 
  public export
  Functor Search where
    map f Stop = Stop
    map f (Go x y) = Go (f x) (map f y)

  public export 
  Applicative Search where
    pure  a = Go a Stop 
    (Go f y) <*> a = map f a
    _ <*> _ = Stop

  public export 
  Monad Search where
    Stop >>= k = Stop
    (Go x y) >>= k = case k x of
                       Stop => y >>= k
                       (Go z w) => Go z w

