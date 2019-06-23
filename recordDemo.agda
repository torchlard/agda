module recordDemo where

-- open import Agda.Builtin.List
open import Data.Nat

data Vec (A : Set) : ℕ -> Set where
  [] : Vec A zero
  _∷_ : ∀{n} -> A -> Vec A n -> Vec A (suc n)

record R : Set where
  field
    {length} : ℕ
    vec : Vec ℕ length

xs : R
xs = record { vec = 0 ∷ 1 ∷ 2 [] }      

ys = record xs {}













