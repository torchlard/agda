module withoutK where

-- this rule is rejected
K : {A : Set} {x : A} (P : x ≡ x -> Set) ->
    P refl -> (x ≡ x : x ≡ x) -> P x≡x
K P p refl = p    

-- accepted
J : {A : Set} (P : (x y : A) -> x ≡ y -> Set) ->
    ((x : A) -> P x x refl) -> (x y : A) (x≡y : x ≡ y) -> P x y x≡y
J P p x .x refl = p x    


-- restrict termination checking
data ⊥ : Set where

mutual 
  data WOne : Set where wrap : FOne -> WOne
  FOne = ⊥ -> WOne

postulate iso : WOne ≡ FOne

-- rejected since at type X, structural descent `f < wrap f` is discounted
noo : (X : Set) -> (WOne ≡ X) -> X -> ⊥
noo .WOne refl (wrap f) = noo FOne iso f













