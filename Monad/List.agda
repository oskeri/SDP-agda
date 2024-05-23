module Monad.List where

open import Monad
open import Function.Base
open import Data.List.Base
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
  hiding ([_])

listFunctor : Functor List
listFunctor = record
  { fmap = map
  ; fmap-id = map-id
  ; fmap-∘ = map-∘
  }

listMonad : Monad List
listMonad = record
  { functor = listFunctor
  ; η = [_]
  ; μ = concat
  ; μ∘η = ++-identityʳ
  ; μ∘mapη = concat-[-]
  ; μ∘μ = sym ∘ concat-concat
  ; map∘η = λ _ _ → refl
  ; map∘μ = λ _ → sym ∘ concat-map
  }
