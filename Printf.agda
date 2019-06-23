module Printf where

open import Data.List using (List; _∷_; [] )
open import Data.Char renaming (Char to Char; show to showC )
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Show renaming (show to showN )
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl )
open import Relation.Nullary using (yes; no)
open import Function

open import Data.String using (toList; fromList; String; _++_)

-- interface
data Fmt : Set where
  fmt : Char -> Fmt   -- formatting char
  lit : Char -> Fmt   -- normat char

-- define format chars
ftype : Char -> Set
ftype 'd' = ℕ
ftype 'c' = Char
ftype _ = ⊥

-- return function to (convert to String according to type)
format : (c : Char) -> ftype c -> String
format 'd' = showN
format 'c' c = fromList $ c ∷ []
format _ = const ""

-- parse sentence
parseF : List Char -> List Fmt
parseF [] = []
parseF ('%' ∷ '%' ∷ xs) = lit '%' ∷ parseF xs
parseF ('%' ∷ c ∷ xs) = fmt c ∷ parseF xs
parseF (c ∷ xs) = lit c ∷ parseF xs

-- construct complete type 
ptype : List Fmt -> Set
ptype [] = String
ptype (fmt x ∷ xs) = ftype x -> ptype xs  -- accumulating types
ptype (lit x ∷ xs) = ptype xs   -- ignore x if normal char

printfType : String -> Set
printfType = ptype ∘ parseF ∘ toList

-- unhandled string, handled string -> convert to string
printfImpl : (fmt : List Fmt) -> String -> ptype fmt
printfImpl [] pref = pref
printfImpl (fmt x ∷ xs) pref val = printfImpl xs (pref ++ format x val)
printfImpl (lit x ∷ xs) pref = printfImpl xs (pref ++ (fromList $ x ∷ []))

printf : (fmt : String) -> printfType fmt
printf s = printfImpl (parseF $ toList s) ""


proof0 : printf "Hello world" ≡ "Hello world"
proof0 = refl

proof1 : printf "%d os" 3 ≡ "3 os"
proof1 = refl

open import IO
main = run $ putStrLn $ printf "%d %c hjk" 12 't'











