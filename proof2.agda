module proof2 where

-- open import Data.Bool using (Bool; if_then_else_; true; false; _∧_)
-- open import Data.Product
-- open import Function.Equality using (_∘_)
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)


+-assoc : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc 0 n p = refl
+-assoc (suc m) n p  rewrite +-assoc  m n p = refl

+-identity' : ∀ (n : ℕ) -> n + 0 ≡ n
+-identity' 0 = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n) 
+-suc' 0 n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm' m 0 rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl



























