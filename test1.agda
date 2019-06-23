module test1 where

open import Data.Nat
open import Data.Nat.Show
open import Data.Bool 
open import Agda.Builtin.List
open import Agda.Builtin.String renaming (primStringAppend to _++_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import IO

-- check : {A : Set} -> A -> Bool
-- check _ = true

a : ℕ
a = 1

-- print : (B : ℕ) -> List B -> String
-- print [] = ""
-- print (x ∷ xs) = (show x) ++ (print xs)

-- main = run ( putStrLn (show (a + 2) ) )
-- main = run ( (filter true []) = [] )

-- p1 : 1 ≡ 1
-- p1 = refl

postulate P : ∀ {A} -> List A -> Set
-- postulate p-nil : P []
-- postulate Q : Set
-- postulate q-nil : Q

-- proof2 : {A : Set} (p : A -> Bool) (xs : List A) -> P (filter p xs) -> Q
-- proof2 p [] _ = q-nil
-- proof2 p (x ∷ xs) H with p x
-- ... | true = -- P (filter p xs) 
-- ... | false = -- P (x ∷ filter p xs) 

-- -- generalisation: all occurrences of term in goal type,argument type generalised

-- compare : Nat -> Nat -> Comparison
-- compare x y with x < y
-- ...          | false with y < x
-- ...            | fales = equal
-- ...            | true = greater
-- compare x y  | true = less


-- compare : Nat -> Nat -> Comparison
-- compare x y with x < y  | y < x
-- ...             | true  | _    = less
-- ...             | _     | true = greater
-- ...             | false | false = equal

postulate plus-commute : (a b : ℕ) -> a + b ≡ b + a

-- record R : Set where
--   coinductive
--   field f : Bool
--         n : ℕ

-- data P (r : R) ℕ -> Set where
--   fTrue : R.f r ≡ true -> P r zero
--   nSuc : P r (suc (R.n r))

-- thm : (a b : ℕ) -> P (a + b) -> P (b + a)
-- thm a b t with  a + b   | plus-commute a b
-- thm a b t    | .(b + a) | refl = t


thm : (a b : ℕ) -> P (a + b) -> P (b + a)
thm a b t rewrite plus-commute a b = t

-- -- =================
-- -- Ill typed with-abstraction

-- postulate
--   A : Set
--   B : A -> Set
--   H : (x : A) -> B x -> Set

-- bad-with : (p : ∑ A B) -> H (fst p) (snd p)  
-- bsd-with p with fst p
-- ...        | _ = 


-- rewirte construction takes term eq of type lhs = rhs
-- expands to with-abstraction of lhs, eq -> follow match of result of eq against refl

postulate T : Nat -> Set

isEven : ℕ -> Bool
isEven 0 = true
isEven (suc 0) = false
isEven (suc (suc n)) = isEven n

thm : (a b : ℕ) -> T (a + b) -> T (b + a)
thm : a b t rewrite plus-commute a b with isEven a
thm a b t | true = t
thm a b t | false = t


data Singleton {a} (A : Set a) {x : A} : Set a where
  _with≡_ : (y : A) -> x ≡ y -> Singleton x

inspect : ∀ {a} {A : Set a} (x : A) -> Singleton x
inspect x = x with≡ refl

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x ∷ xs) with inspect (p x)
...                 | true  with≡ eq =
...                 | false with≡ eq =

-- ===== VS =======

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs


module _ {a b} {A : Set a} {B : A -> Set b} where
  data Graph (f : ∀ x -> B x) (x : A) (y : B x) : Set b where
    ingraph : f x ≡ y -> Graph f x y

  inspect : (f : ∀ x -> B x) (x : A) -> Graph f x (f x)
  inspect _ _ = ingraph refl










