module Synthesis.Util

import Core.Core

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


