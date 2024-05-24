module SDP.SDP where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures
open import Algebra.Structures

open import Finite
open import Monad

private variable
  t n : ℕ
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

-- Representations of SDP:s, parameterized over a monad

record SDP {M} (isMonad : Monad M) : Set₁ where

  open Monad.Monad isMonad public

  field
    -- States
    X : ℕ → Set
    -- Controls
    Y : X t → Set
    -- Computing the next state(s)
    next : (x : X t) → Y x → M (X (suc t))
    -- A total preorder of values
    value : Value

  open Value value public

  field
    -- A reward function
    reward : (x : X t) → Y x → X (suc t) → Val
    -- An aggregation function for values
    measure : M Val → Val

-- Representation of SDP:s with finite and non-empty controls

record Finite-SDP {M} (isMonad : Monad M) : Set₁ where
  field
    sdp : SDP isMonad

  open SDP sdp public

  field
    Y-finite : ∀ {t} → (x : X t) → Σ ℕ λ n → Finite (suc n) (Y x)
