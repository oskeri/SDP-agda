-- Finite types

module Finite where

open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Vec.Base
open import Data.Vec.Properties
open import Data.Product.Base hiding (map)
open import Relation.Binary.PropositionalEquality

private variable
  A : Set
  n : ℕ

-- Finite types of n elements

record Finite (n : ℕ) (A : Set) : Set where
  field
    toFin : A → Fin n
    fromFin : Fin n → A
    to∘from : ∀ x → toFin (fromFin x) ≡ x
    from∘to : ∀ a → fromFin (toFin a) ≡ a

  -- Get a list of all elements of A

  toVec : Vec A n
  toVec = map fromFin (allFin _)

  -- Every element of A is in toVec

  inAllFin : (a : A) → a ≡ fromFin (lookup (allFin _) (toFin a))
  inAllFin a rewrite lookup-allFin (toFin a) = sym (from∘to a)
