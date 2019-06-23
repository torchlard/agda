{-# OPTIONS --without-K #-}
module ch1-ex2 where

open import Data.Product
open import Relation.Binary.PropositionalEquality

module ×-Rec {i j k} {A : Set i} {B : Set j} {C : Set k}
              (d : A -> B -> C) where

  ×-rec : A × B -> C
  ×-rec p = d (proj₁ p) (proj₂ p)

  ×-rec-b : (x : A) -> (y : B) -> ×-rec (x , y) ≡ d x y
  ×-rec-b x y = refl


module Σ-Rec {i j k} {A : Set i} {B : A -> Set j} {C : Set k}
              (d : (x : A) -> B x -> C) where
  
  Σ-rec : Σ A B -> C
  Σ-rec p = d (proj₁ p) (proj₂ p)

  Σ-rec-b : (x : A) -> (y : B x) -> Σ-rec (x , y) ≡ d x y
  Σ-rec-b x y = refl








