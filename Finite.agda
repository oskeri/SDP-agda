{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Finite types
------------------------------------------------------------------------

module Finite where

open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Unit.Base
open import Data.Vec.Base
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality

-- Finite types of n elements

record Finite (n : ℕ) (A : Set) : Set where
  field
    toFin : A → Fin n
    fromFin : Fin n → A
    to∘from : ∀ x → toFin (fromFin x) ≡ x
    from∘to : ∀ a → fromFin (toFin a) ≡ a

  -- Get a list of all elements of A

  all : Vec A n
  all = map fromFin (allFin _)

  -- Every element of A is in toVec

  inAllFin : (a : A) → a ≡ fromFin (lookup (allFin _) (toFin a))
  inAllFin a rewrite lookup-allFin (toFin a) = sym (from∘to a)

-- The unit type is finite (and has one element)

⊤-finite : Finite 1 ⊤
⊤-finite = record
  { toFin = λ _ → zero
  ; fromFin = λ _ → tt
  ; to∘from = λ { zero → refl }
  ; from∘to = λ { tt → refl }
  }
