module Value where

open import Relation.Binary.Structures
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Reasoning.Preorder

private variable
  A : Set

-- Values

record Value : Set₁ where
  field
    Val : Set
    -- Values are a monoid
    𝟘 : Val
    _⊕_ : Val → Val → Val
    Val-monoid : IsMonoid _≡_ _⊕_ 𝟘
    -- Values have a total preorder
    _≤_ : Val → Val → Set
    Val-preorder : IsTotalPreorder _≡_ _≤_

    -- _⊕_ is monotone
    ⊕-mon : ∀ {a b c d} → a ≤ b → c ≤ d
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

  open IsMonoid Val-monoid public
    using ()
  open IsTotalPreorder Val-preorder public
    using ()
    renaming (refl to ≤-refl; trans to ≤-trans; total to ≤-total)
