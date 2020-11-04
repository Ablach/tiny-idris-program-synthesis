module Synthesis.SynthErr

import Core.TT
import Core.Value


public export
data SynthErr : Type where
  NotInContext    : (tm : Name     ) -> SynthErr 
  NotHole         : (tm : Name     ) -> SynthErr
  AlreadyDefined  : (tm : Term []  ) -> SynthErr
  NoMatch         :                     SynthErr
  Impossible      : String           -> SynthErr

export
Show SynthErr where
  show (NotInContext tm) = "Not in context" ++ show tm
  show (NotHole tm) = "Not a hole" ++ show tm
  show (AlreadyDefined tm) = "Already defined" ++ show tm
  show NoMatch = "No match"
  show (Impossible st) = "Impossible -- " ++ st
