module enum where

-- {-# BUILTIN NATURAL ℕ #-}
open import Data.Bool
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

record Enumeration (A : Set) : Set where
  constructor enumeration
  field
    start : A
    forward : A -> A
    backward : A -> A

open Enumeration

3rd : {A : Set} -> Enumeration A -> A
3rd e = forward e (forward e (forward e (start e)))

    
-- open Enumeration

-- enum-Nat : Enumeration ℕ
-- enum-Nat = record {
--     start    = 0 ;
--     forward  = suc ;
--     backward = predc
--   } where
--       predc : ℕ -> ℕ
--       predc zero    = zero
--       predc (suc x) = x


-- ======= copatterns =======


enum-Nat : Enumeration ℕ
start enum-Nat = 0
forward enum-Nat n = suc n
backward enum-Nat 0 = 0
backward enum-Nat (suc n) = n

test1 : 3rd enum-Nat ≡ 3
test1 = refl



enum-Nat2 : ℕ -> Enumeration ℕ
start (enum-Nat2 init) = init
forward (enum-Nat2 _) n = suc n
backward (enum-Nat2 _) 0 = 0
backward (enum-Nat2 _) (suc n) = n

test2 : 3rd (enum-Nat2 10) ≡ 13
test2 = refl


-- restrict user to start from 0 / 42
enum-Nat3 : Bool -> Enumeration ℕ
start (enum-Nat3 true) = 0
start (enum-Nat3 false) = 42
forward (enum-Nat3 _) n = suc n
backward (enum-Nat3 _) 0 = 0
backward (enum-Nat3 _) (suc n) = n

test3 : 3rd (enum-Nat3 true) ≡ 3
test3 = refl












