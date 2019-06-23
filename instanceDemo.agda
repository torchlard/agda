module instanceDemo where

open Monoid {{...}} public

mempty : ∀ {a} {A : Set a} {{_ : Monoid A}} -> A
_<>_ : ∀ {a} {A : Set a} {{_ : Monoid A}} -> A -> A -> A

mconcat : ∀ {a} {A : Set a} {{_ : Monoid A}} -> List A -> A
mconcat [] = mempty
mconcat (x ∷ xs) = x <> (mconcat xs)

sum : List ℕ -> ℕ
sum xs =
  let instance
    NatMonoid : Monoid ℕ
    NatMonoid = record { mempty = 0; _<>_ = _+_ }
  in mconcat xs


data Fin : ℕ -> Set where
  zero : ∀ {n} -> Fin (suc n)
  suc : ∀ {n} -> Fin n -> Fin (suc n)

mkFin : ∀ {n} (m : ℕ) {{_ : suc m - n ≡ 0}} -> Fin n
mkFin {zero} m {{}}
mkFin {suc n} zero = zero
mkFin {suc n} (suc m) = suc (mkFin m)

five : Fin 6
five = mkFin 5









