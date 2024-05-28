------------------------------------------------------------------------
-- The identity monad
------------------------------------------------------------------------

module Monad.Identity where

open import Monad
open import Agda.Builtin.Equality

Id : Set → Set
Id A = A

idFunctor : Functor Id
idFunctor = record
  { fmap = λ f x → f x
  ; fmap-id = λ _ → refl
  ; fmap-∘ = λ _ → refl
  }

idMonad : Monad Id
idMonad = record
  { functor = idFunctor
  ; η = λ x → x
  ; μ = λ x → x
  ; μ∘η = λ _ → refl
  ; μ∘mapη = λ _ → refl
  ; μ∘μ = λ _ → refl
  ; map∘η = λ _ _ → refl
  ; map∘μ = λ _ _ → refl
  }
