-- Computing maximum values of functions where the domain is finite and non-empty

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

open import Data.Nat.Base hiding (_≤_)

open import Finite

module Finite.Max
  {n} {A V : Set} {_≤_ : V → V → Set}
  (V-preorder : IsTotalPreorder _≡_ _≤_)
  (fin : Finite (suc n) A)
  where

open Finite.Finite fin

import Max V-preorder as M
open import Data.Fin.Base hiding (_≤_)
open import Data.Vec.Base
open import Data.Vec.Properties
open import Relation.Binary.Reasoning.Preorder
  (record { Carrier = V ; _≈_ = _≡_ ; _≲_ = _≤_
          ; isPreorder = IsTotalPreorder.isPreorder V-preorder })


max : (f : A → V) → V
max f = M.max f toVec

argmax : (f : A → V) → A
argmax f = M.argmax f toVec

max-argmax : (f : A → V) → max f ≡ f (argmax f)
max-argmax f = M.max-argmax f toVec

≤-max : (f : A → V) (a : A) → f a ≤ max f
≤-max f a = begin
  f a
    ≡⟨ cong f (inAllFin a) ⟩
  f (fromFin (lookup (allFin _) (toFin a)))
    ≡˘⟨ cong f (lookup-map (toFin a) fromFin (allFin _)) ⟩
  f (lookup (map fromFin (allFin _)) (toFin a))
    ≡⟨⟩
  f (lookup toVec (toFin a))
    ∼⟨ M.≤-max f toVec (toFin a) ⟩
  max f ∎
