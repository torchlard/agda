{-# OPTIONS --without-K #-}
module ch1-ex1 where

open import Relation.Binary.PropositionalEquality 


_∘_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
      -> (B -> C) -> (A -> B) -> (A -> C)
g ∘ f = λ x -> g (f x)


∘-assoc : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
          -> (h : C -> D) -> (g : B -> C) -> (f : A -> B)
          -> h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc f g h = refl          











