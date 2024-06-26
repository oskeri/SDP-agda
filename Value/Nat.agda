{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Natural numbers as a Value instance
------------------------------------------------------------------------

module Value.Nat where

open import Value

open import Data.Nat.Base
open import Data.Nat.Properties

ℕ-value : Value ℕ
ℕ-value = record
  { 𝟘 = 0
  ; _⊕_ = _+_
  ; _≤_ = _≤_
  ; Val-preorder = ≤-isTotalPreorder
  ; ⊕-mono = +-mono-≤
  }
