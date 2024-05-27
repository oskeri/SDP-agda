module SDP.SDP where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base

open import Value public
open import Finite
open import Monad

private variable
  t n : ℕ

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

  open Value.Value value public

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
