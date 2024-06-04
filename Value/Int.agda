{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Integers as a Value instance
------------------------------------------------------------------------

module Value.Int where

open import Value

open import Data.Integer.Base
open import Data.Integer.Properties

-- Integers with normal addition

ℤ-value-+ : Value ℤ
ℤ-value-+ = record
  { 𝟘 = 0ℤ
  ; _⊕_ = _+_
  ; _≤_ = _≤_
  ; Val-preorder = ≤-isTotalPreorder
  ; ⊕-mono = +-mono-≤
  }

-- Integers where a ⊕ b = a
-- This corresponds to the value being given only by the final state

ℤ-valueʳ : Value ℤ
ℤ-valueʳ = record
  { 𝟘 = 0ℤ
  ; _⊕_ = λ x y → x
  ; _≤_ = _≤_
  ; Val-preorder = ≤-isTotalPreorder
  ; ⊕-mono = λ a≤b c≤d → a≤b
  }
