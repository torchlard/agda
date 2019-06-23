module peano where

{-# BUILTIN NATURAL ℕ #-}

open import Relation.Binary.PropositionalEquality as Eq
-- open import IO
-- open import Data.Nat.Show

-- data ℕ : Set where
--   zero : ℕ
--   suc  : ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
zero + zero = zero
zero + n = n
(suc n) + n1 = suc (n + n1)

-- eg. 5+3 = (suc 4)+3 = suc (3+3) = suc((suc 2)+3) = suc(suc (suc (1)+3)) =suc(suc(suc(suc 0+3))))))
-- suc(suc(suc(suc(suc 3)))) = 8

-- -- main = run ( putStrLn ( show (suc zero) ))
-- main = run (putStrLn ( show 10 ))

-- bring std lib module that defines equality into scope
open Eq using (_≡_; refl)
-- xx_=prefix, _x_=infix, _xx=postfix
-- langle⟨, rangle⟩
-- open Eq.≣-Reasoning using (begin_; _≣⟨⟩_ ; _∎)   

-- dummy name _
_ : 2 + 3 ≣ 5
-- _ =
--   begin
--     2 + 3
--   ≣()
--     -- (suc (suc zero)) + (suc (suc (suc zero)))
--     suc (1 + 3)
--   ≡()
--     suc (suc (0 + 3))
--   ≡()
--     suc (suc 3)
--   ≣()
--     5
--   ∎
_ = refl


-- avoid writing too many parentheses
-- precedence level 6
infixl 6  _+_ _∸_
infixl 7  _*_


{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}




