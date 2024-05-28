module SDP.SDP where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base
open import Data.Vec.Base

open import Value public
open import Finite
open import Monad

private variable
  t n : ℕ
  A : Set

-- Representations of SDP:s, parameterized over a monad

record SDP {M} (isMonad : Monad M) : Set₁ where

  open Monad.Monad isMonad public

  field
    -- States
    State : ℕ → Set
    -- Controls
    Ctrl : State t → Set
    -- Computing the next state(s)
    next : (x : State t) → Ctrl x → M (State (suc t))
    -- A total preorder of values
    value : Value

  open Value.Value value public

  field
    -- A reward function
    reward : (x : State t) → Ctrl x → State (suc t) → Val
    -- An aggregation function for values
    measure : M Val → Val

    -- Measure is monotone
    measure-mon : {f g : A → Val}
                → f ≤ₗ g → (a : M A)
                → measure (fmap f a) ≤ measure (fmap g a)

-- Representation of SDP:s with finite and non-empty controls

record Finite-SDP {M} (isMonad : Monad M) : Set₁ where
  field
    sdp : SDP isMonad

  open SDP sdp public

  field
    Ctrl-finite : ∀ {t} → (x : State t) → Σ ℕ λ n → Finite (suc n) (Ctrl x)

  -- A vector containing all controls of a given state

  allCtrls : (x : State t) → Vec (Ctrl x) _
  allCtrls x = Finite.all (Ctrl-finite x .proj₂)
