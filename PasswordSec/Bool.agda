module PasswordSec.Bool where

open import Data.Bool
open import Data.Nat

nat-of-bool : Bool -> ℕ
nat-of-bool false = 0
nat-of-bool true = 1
