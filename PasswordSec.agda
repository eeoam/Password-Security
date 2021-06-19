module PasswordSec where

open import Agda.Builtin.Char
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty

open import Data.Product hiding (map)
private variable A B : Set

∃l : (A × B -> Set) -> Set
∃l = ∃

∅ : List Char -> Set
∅ w = ⊥

` : Char -> List Char -> Set
` c w = w ≡ [ c ]

open import Data.Sum hiding (map)

infixr 6 _∪_
_∪_ : (List Char -> Set) -> (List Char -> Set) -> List Char -> Set
(P ∪ Q) w = P w ⊎ Q w

infixl 7 _·_
_·_ : (List Char -> Set) -> (List Char -> Set) -> List Char -> Set
(P · Q) w = ∃l \ (u , v) -> (w ≡ u ++ v) × P u × Q v

mk : List Char -> List Char -> Set
mk xs = foldl _·_ ∅ (map ` xs)

open import Data.String

badliterals : List Char -> Set
badliterals = mk (toList "password") ∪
              mk (toList "123456")


badpasswords : List Char -> Set
badpasswords = badliterals

-- How to capture the following properties with dependent types?
-- if xs is a bad password, than so is reverse xs
-- if xs is a bad password, than so is l33t xs
-- if xs is a palindrome then it is a bad password
-- if xs = ys+ for some ys then xs is a bad password
-- if xs == sort xs then xs is a bad password
