------------------------------------------------------------------------
-- Solving SDP:s using backwards induction given a function that finds
-- an optimal policy to extend a policy sequence.
------------------------------------------------------------------------

open import SDP.SDP
import SDP.Policy
open import Monad

module SDP.BackwardsInduction
  {M} {isMonad : Monad M}
  (sdp : SDP isMonad)
  (open SDP.Policy sdp)
  (isOptExtFun : optExtFun)
  where

open optExtFun isOptExtFun
open SDP sdp

open import Data.Nat.Base

private variable
  t n : ℕ

-- Solving SDP:s using backwards induction

bi : (t n : ℕ) → PolicySeq t n
bi t zero = []
bi t (suc n) =
  let ps = bi (suc t) n
  in  optExt ps ∷ ps

-- The solution is an optimal policy sequence

biOptVal : (t n : ℕ) → OptPolicySeq (bi t n)
biOptVal t zero [] _ = ≤-refl
biOptVal t (suc n) (p ∷ ps) x = begin
  val (p ∷ ps) x
    ≡⟨⟩
  measure (fmap (reward x y ⊕ₗ val ps) (next x y))
    ≲⟨ measure-mon (λ x′ → ⊕-mon ≤-refl (biOptVal (suc t) n ps x′)) (next x y) ⟩
  measure (fmap (reward x y ⊕ₗ val ps′) (next x y))
    ≡⟨⟩
  val (p ∷ ps′) x
    ≲⟨ optExtSpec ps′ p x ⟩
  val (p′ ∷ ps′) x
    ≡⟨⟩
  val (bi t (suc n)) x ∎
  where
  y = p x
  p′ = optExt (bi (suc t) n)
  ps′ = bi (suc t) n
  y′ = p′ x
  open ≤-Reasoning
