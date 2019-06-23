module hello where

-- open import Agda.Builtin.IO
-- open import Agda.Builtin.Unit
-- open import Agda.Builtin.String

-- postulate
--   putStrLn : String → IO ⊤

-- {-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
-- {-# COMPILE GHC putStrLn = Text.putStrLn #-}

-- main : IO ⊤
-- main = putStrLn "Hello, world!"

open import IO
main = run ( putStrLn "Hello, worl!" )





