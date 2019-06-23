module plfa-relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- z≤n and s≤s are constructor names
-- zero ≤ n, suc m ≤ suc n are types
-- indexed data type: type (m ≤ n) indexed by m,n

-- ∀n:N, constructor z≤n rpovide evidence that zero ≤ n holds
-- ∀m,n : N, constructor s≤s takes evidence that m ≤ n holds

_ : 2 ≤ 4
_ = s≤s {n=3} (s≤s {n = 2} z≤n)

infix 4 _≤_













