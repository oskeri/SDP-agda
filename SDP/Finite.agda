open import SDP.SDP
open import Monad

-- Properties of finite SDP:s

module SDP.Finite
  {M} {isMonad : Monad M}
  (fsdp : Finite-SDP isMonad)
  where

open Finite-SDP fsdp

open import Finite
open import Max Val-preorder
open import SDP.Policy sdp

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base
open import Data.Vec.Base
open import Data.Vec.Properties
open import Data.Product.Base hiding (map)


private
  variable
    t n : ℕ

  val′ : (x : State t) (ps : PolicySeq (suc t) n) (y : Ctrl x) → Val
  val′ x ps y = measure (fmap (reward x y ⊕ₗ val ps) (next x y))

-- Computing a policy to extend a sequence

optExt : PolicySeq (suc t) n → Policy t
optExt ps x = argmax (val′ x ps) (allCtrls x)

-- The policy given by optExt is an optimal extension

optExtSpec : (ps : PolicySeq (suc t) n) → OptExt ps (optExt ps)
optExtSpec ps p′ x = begin
  val (p′ ∷ ps) x
    ≡⟨⟩
  val′ x ps (p′ x)
    ≡⟨ cong (val′ x ps) (inAllFin (p′ x)) ⟩
  val′ x ps (fromFin (lookup (allFin _) (toFin (p′ x))))
    ≡˘⟨ cong (val′ x ps) (lookup-map (toFin (p′ x)) fromFin (allFin _)) ⟩
  val′ x ps (lookup (map fromFin (allFin _)) (toFin (p′ x)))
    ≡⟨⟩
  val′ x ps (lookup (allCtrls x) (toFin (p′ x)))
    ≲⟨ ≤-max (val′ x ps) (allCtrls x) (toFin (p′ x)) ⟩
  max (val′ x ps) (allCtrls x)
    ≡⟨ max-argmax (val′ x ps) (allCtrls x) ⟩
  val′ x ps (argmax (val′ x ps) (allCtrls x))
    ≡⟨⟩
  val′ x ps (optExt ps x) ≡⟨⟩
  val (optExt ps ∷ ps) x ∎
  where
  open ≤-Reasoning
  open Finite.Finite (Ctrl-finite x .proj₂)

isOptExtFun : optExtFun
isOptExtFun = record
  { optExt = optExt
  ; optExtSpec = optExtSpec
  }
