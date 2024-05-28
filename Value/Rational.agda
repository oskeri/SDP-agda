------------------------------------------------------------------------
-- Rational numbers as a Value instance
------------------------------------------------------------------------

module Value.Rational where

open import Value
open import Data.Rational.Base
open import Data.Rational.Properties

ℚ-value : Value
ℚ-value = record
  { Val = ℚ
  ; 𝟘 = 0ℚ
  ; _⊕_ = _+_
  ; _≤_ = _≤_
  ; Val-preorder = ≤-isTotalPreorder
  ; ⊕-mon = +-mono-≤
  }
