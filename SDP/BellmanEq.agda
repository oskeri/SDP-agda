open import SDP.SDP
open import Monad.Identity
open import Relation.Binary.PropositionalEquality

-- Proof of Bellman's equation for the alternative value function val′
-- when the identity monad is used and measure is the identity function.

module SDP.BellmanEq
  (sdp : SDP idMonad)
  (open SDP sdp)
  (measure≡id : ∀ x → measure x ≡ x)
  where

open import SDP.Policy sdp hiding (BellmanEq)
open import SDP.Trajectory sdp

open import Data.Nat.Base

private variable
  t n : ℕ

sumTrj-⊕ : (p : Policy t) (ps : PolicySeq (suc t) n) (x : X t)
         → sumTrj (trj (p ∷ ps) x) ≡ reward x (p x) (next x (p x)) ⊕ val′ ps (next x (p x))
sumTrj-⊕ p ps x =
  cong₂ _⊕_ (cong (reward x (p x)) (lemma p ps x)) (sym (measure≡id _))
  where
  lemma : ∀ p ps x → head (next x (p x) >>= trj ps) ≡ next x (p x)
  lemma p [] x = refl
  lemma p (p′ ∷ ps) x = refl


BellmanEq : (p : Policy t) (ps : PolicySeq (suc t) n) (x : X t)
          → val′ (p ∷ ps) x ≡ measure (fmap (reward x (p x) ⊕ₗ val′ ps) (next x (p x)))
BellmanEq p ps x = cong measure (sumTrj-⊕ p ps x)
