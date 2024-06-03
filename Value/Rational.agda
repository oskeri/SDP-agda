{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Rational numbers as a Value instance
------------------------------------------------------------------------

module Value.Rational where

open import Value

open import Data.Integer.Base using (1ℤ)
open import Data.List.Base
open import Data.Rational.Base public
open import Data.Rational.Properties
open import Data.Rational.Literals
open import Agda.Builtin.FromNat
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base

private variable
  A : Set
  f g : A → ℚ

ℚ-value : (_⊕_ : ℚ → ℚ → ℚ) → (∀ {a b c d} → a ≤ b → c ≤ d → (a ⊕ c) ≤ (b ⊕ d))
        → Value ℚ
ℚ-value _⊕_ ⊕-mono = record
  { 𝟘 = 0ℚ
  ; _⊕_ = _⊕_
  ; _≤_ = _≤_
  ; Val-preorder = ≤-isTotalPreorder
  ; ⊕-mono = ⊕-mono
  }

-- Rationals with normal addition

ℚ-value-+ : Value ℚ
ℚ-value-+ = ℚ-value _+_ +-mono-≤

-- Rationals where the right argument of _⊕_ is scaled by ½

ℚ-value-+½ : Value ℚ
ℚ-value-+½ =
  ℚ-value (λ a b → a + ½ * b) λ a≤b c≤d →
    +-mono-≤ a≤b (*-monoˡ-≤-nonNeg ½ c≤d)


-- Converting natural numbers to rationals

ℕ→ℚ : ℕ → ℚ
ℕ→ℚ n = Number.fromNat number n ⦃ _ ⦄

-- The average of a list of numbers
-- In the case of the empty list, the average is defined to be 0

avg : List ℚ → ℚ
avg [] = 0ℚ
avg qs@(x ∷ xs) = (foldr _+_ 0ℚ qs ÷ ℕ→ℚ (length qs)) ⦃ _ ⦄

-- A function that can be used to compute the expecation value from the SP monad
-- see the module EV in Monad.SP.

-- Note that if the total weight is zero, the expectation value will be zero

ev-helper : ℕ → (ℕ × ℚ) → ℚ
ev-helper zero (w , q) = 0ℚ
ev-helper wₜₒₜ@(suc _) (w , q) = (ℕ→ℚ w * q ÷ ℕ→ℚ wₜₒₜ) ⦃ _ ⦄

-- The helper function is monotone

ev-helper-mono : (f≤g : (a : A) → f a ≤ g a) (w w′ : ℕ) (a : A)
               → ev-helper w (w′ , f a) ≤ ev-helper w (w′ , g a)
ev-helper-mono f≤g zero w′ a = ≤-refl
ev-helper-mono {f} {g} f≤g (suc w) zero a
  rewrite *-zeroˡ (f a)
  rewrite *-zeroˡ (g a) = ≤-refl
ev-helper-mono f≤g (suc w) (suc w′) a =
  *-monoʳ-≤-nonNeg (1/ ℕ→ℚ (suc w)) (*-monoˡ-≤-nonNeg (ℕ→ℚ (suc w′)) (f≤g a))
