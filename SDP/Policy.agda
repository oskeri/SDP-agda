open import SDP.SDP
open import Monad

module SDP.Policy {M} {isMonad : Monad M} (sdp : SDP isMonad) where

open SDP sdp

open import Data.Nat.Base
open import Agda.Builtin.Equality

private variable
  t n : ℕ

-- Policies

Policy : ℕ → Set
Policy t = (x : X t) → Y x

-- Policy sequences

data PolicySeq (t : ℕ) : (n : ℕ) → Set where
  [] : PolicySeq t 0
  _∷_ : (p : Policy t) → (ps : PolicySeq (suc t) n) → PolicySeq t (suc n)

infixr 5 _∷_

-- Computing the value of a policy sequence

val : PolicySeq t n → X t → Val
val [] x = 𝟘
val (p ∷ ps) x =
  let y = p x
      mx′ = next x y
  in  measure (fmap (reward x y ⊕ₗ val ps) mx′)

-- Note that Bellman's equality holds definitionally with this definition of val

BellmanEq : (p : Policy t) (ps : PolicySeq (suc t) n) (x : X t)
          → val (p ∷ ps) x ≡ measure (fmap (reward x (p x) ⊕ₗ val ps) (next x (p x)))
BellmanEq p ps x = refl

-- Optimal policy sequences

OptPolicySeq : PolicySeq t n → Set
OptPolicySeq {t} {n} ps = (ps′ : PolicySeq t n) → val ps′ ≤ₗ val ps

-- Optimal extensions

OptExt : PolicySeq (suc t) n → Policy t → Set
OptExt ps p = ∀ p′ → val (p′ ∷ ps) ≤ₗ val (p ∷ ps)
