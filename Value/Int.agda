{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Integers as a Value instance
------------------------------------------------------------------------

module Value.Int where

open import Value

open import Data.Integer.Base
open import Data.Integer.Properties

ℤ-value : Value ℤ
ℤ-value = record
  { 𝟘 = 0ℤ
  ; _⊕_ = _+_
  ; _≤_ = _≤_
  ; Val-preorder = ≤-isTotalPreorder
  ; ⊕-mono = +-mono-≤
  }
