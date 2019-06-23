module universeDemo where

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B  


-- need to define special List, because List Set cannot be a Set
-- so List Set is not valid type
data List₁ (A : Set₁) : Set₁ where
  [] : List₁ A
  _::_ : A -> List₁ A -> List₁ A


Prod : List₁ Set -> Set
Prod [] = ⊤
Prod (A :: As) = A × Prod As


-- Universe polymorphism

open import Agda.Primitive

data List {n : Level} (A : Set n) : Set n where
  [] : List A
  _::_ : A -> List A -> List A








