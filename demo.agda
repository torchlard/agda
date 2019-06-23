module demo where


open import Data.Nat
open import Data.Bool using (Bool; if_then_else_; true; false; _∧_)
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open Eq using (_≡_; refl; cong; sym)
open import Function.Equality using (_∘_)

data exp :  Set where
  NConst : ℕ -> exp
  Plus : exp -> exp -> exp
  Mult : exp -> exp -> exp

expDenote : exp -> ℕ
expDenote  (NConst x) = x
expDenote  (Plus e e₁) = expDenote e + expDenote e₁
expDenote  (Mult e e₁) = expDenote e * expDenote e₁

smartplus : exp -> exp -> exp
smartplus (NConst n1) (NConst n2)  = NConst (n1 + n2)
smartplus e1 e2 = Plus e1 e2

spcorrect : ∀ e1 e2 -> expDenote (smartplus e1 e2) ≡ expDenote e1 + expDenote e2
spcorrect (NConst x) (NConst x₁) = refl
spcorrect (NConst x) (Plus e2 e3) = refl
spcorrect (NConst x) (Mult e2 e3) = refl
spcorrect (Plus e1 e3) e2 = refl
spcorrect (Mult e1 e3) e2 = refl

spcong : ∀ e1 e1' e2 e2' ->
         expDenote e1 ≡ expDenote e1' ->
         expDenote e2 ≡ expDenote e2' ->
         expDenote (smartplus e1 e2) ≡ expDenote (smartplus e1' e2')
spcong e1 e1' e2 e2' eq eq' = begin
  expDenote (smartplus e1 e2)
  ≡⟨ spcorrect e1 e2 ⟩
  expDenote e1 + expDenote e2
  ≡⟨ cong (λ x -> x + expDenote e2) eq ⟩
  expDenote e1' + expDenote e2
  ≡⟨ cong (λ x -> expDenote e1' + x ) eq' ⟩
  expDenote e1' + expDenote e2'
  ≡⟨ sym (spcorrect e1' e2') ⟩
  expDenote (smartplus e1' e2')
∎
