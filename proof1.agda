module proof1 where

-- open import Data.Bool using (Bool; if_then_else_; true; false; _∧_)
-- open import Data.Product
-- open import Function.Equality using (_∘_)
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open Eq using (_≡_; refl; cong; sym)

_ : 2 + 3 ≡ 5
_ = begin
   2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

+-assoc : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc 0 n p =
  begin
    (0 + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    0 + (n + p)
  ∎
+-assoc (suc m) n p =
  begin (suc m + n) + p
  ≡⟨⟩ suc (m + n) + p
  ≡⟨⟩ suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩ suc (m + (n + p))
  ≡⟨⟩ suc m + (n + p)
  ∎


+-assoc2 : ∀ (n p : ℕ) -> (2 + n) + p ≡ 2 + (n + p)
+-assoc2 n p =
  begin (2 + n) + p
  ≡⟨⟩ suc (1 + n) + p
  ≡⟨⟩ suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc1 n p) ⟩  suc (1 + (n + p))
  ≡⟨⟩ 2 + (n + p)
  ∎
  where
  +-assoc1 : ∀ (n p : ℕ) -> (1 + n) + p ≡ 1 + (n + p)
  +-assoc1 n p =
    begin (1 + n) + p
    ≡⟨⟩ suc (0 + n) + p
    ≡⟨⟩ suc ((0 + n) + p)
    ≡⟨ cong suc (+-assoc0 n p) ⟩ suc (0 + (n + p))
    ∎
    where
    +-assoc0 : ∀ (n p : ℕ) -> (0 + n) + p ≡ 0 + (n + p)
    +-assoc0 n p =
      begin (0 + n) + p
      ≡⟨⟩ n + p
      ≡⟨⟩ 0 + (n + p)
      ∎


+-iden : ∀ (m : ℕ) -> m + 0 ≡ m
+-iden 0 = 
  begin 0 + 0
  ≡⟨⟩ 0
  ∎
+-iden (suc m) =
  begin suc m + 0
  ≡⟨⟩ suc (m + 0)  
  ≡⟨ cong suc (+-iden m) ⟩ suc m
  ∎

+-succ : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)
+-succ 0 n =
  begin 0 + suc n
  ≡⟨⟩ suc n
  ≡⟨⟩ suc (0 + n)
  ∎
+-succ (suc m) n =
  begin (suc m) + (suc n)
  ≡⟨⟩ suc (m + suc n)
  ≡⟨ cong suc (+-succ m n) ⟩ suc (suc (m + n))
  ≡⟨⟩ suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm m 0 = 
  begin m + 0
  ≡⟨ +-iden m ⟩ m
  ≡⟨⟩ 0 + m
  ∎
+-comm m (suc n) =
  begin m + suc n
  ≡⟨ +-succ m n ⟩ suc (m + n) 
  ≡⟨ cong suc (+-comm m n) ⟩ suc (n + m)
  ≡⟨⟩ suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
    -- sym: reverse
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎






 












