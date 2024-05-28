------------------------------------------------------------------------
-- Integers as a Value instance
------------------------------------------------------------------------

module Value.Int where

open import Value

open import Data.Integer.Base
open import Data.Integer.Properties

ℕ-value : Value
ℕ-value = record
  { Val = ℤ
  ; 𝟘 = 0ℤ
  ; _⊕_ = _+_
  ; Val-monoid = +-0-isMonoid
  ; _≤_ = _≤_
  ; Val-preorder = ≤-isTotalPreorder
  ; ⊕-mon = +-mono-≤
  }
