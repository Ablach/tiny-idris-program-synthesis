open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])

data Test : Set where
  c1 : ⊥ -> Test
  c2 : (v1 : List Bool) -> (v2 : List ℕ) -> length (v1 ++ [ true ]) ≡ length ((1 ∷ 2 ∷ []) ++ v2) -> Test

test : Test
test = ?
