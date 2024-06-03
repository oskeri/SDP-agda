{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- The type of values of SDP:s
------------------------------------------------------------------------

module Value where

open import Relation.Binary.Structures
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Reasoning.Preorder

private variable
  A : Set

-- Values

record Value (Val : Set) : Set₁ where
  field
    -- There is a zero value
    𝟘 : Val
    -- There is "addition" for values
    _⊕_ : Val → Val → Val

    -- Values have a total preorder
    _≤_ : Val → Val → Set
    Val-preorder : IsTotalPreorder _≡_ _≤_

    -- _⊕_ is monotone
    ⊕-mono : ∀ {a b c d} → a ≤ b → c ≤ d
           → a ⊕ c ≤ b ⊕ d

  module ≤-Reasoning = Relation.Binary.Reasoning.Preorder
    (record { Carrier = Val ; _≈_ = _≡_ ; _≲_ = _≤_
            ; isPreorder = IsTotalPreorder.isPreorder Val-preorder })

  -- Lifted monoidal operation to functions
  _⊕ₗ_ : (f g : A → Val) → A → Val
  f ⊕ₗ g = λ a → f a ⊕ g a

  -- Lifted order relation to functions
  _≤ₗ_ : (f g : A → Val) → Set
  f ≤ₗ g = ∀ a → f a ≤ g a

  infixl 7 _⊕_
  infixl 7 _⊕ₗ_
  infix  4 _≤_
  infix  4 _≤ₗ_

  open IsTotalPreorder Val-preorder public
    using ()
    renaming (refl to ≤-refl; trans to ≤-trans; total to ≤-total)
