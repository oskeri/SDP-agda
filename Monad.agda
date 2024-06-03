{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Definition of functors and monads
------------------------------------------------------------------------

module Monad where

open import Function.Base
open import Agda.Builtin.Equality

private variable
  A B C : Set
  f g : A → B

-- Functors

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : (f : A → B) → F A → F B
    fmap-id : (x : F A) → fmap id x ≡ x
    fmap-∘ : (x : F A) → fmap (f ∘ g) x ≡ fmap f (fmap g x)

-- Monads

record Monad (M : Set → Set) : Set₁ where
  field
    functor : Functor M
    -- return/pure
    η : A → M A
    -- join
    μ : M (M A) → M A

  open Functor functor public

  field
    -- Laws of the operations
    μ∘η : (x : M A) → μ (η x) ≡ x
    μ∘mapη : (x : M A) → μ (fmap η x) ≡ x
    μ∘μ : (x : M (M (M A))) → μ (μ x) ≡ μ (fmap μ x)
    map∘η : (f : A → B) (x : A) → fmap f (η x) ≡ η (f x)
    map∘μ : (f : A → B) (x : M (M A)) → fmap f (μ x) ≡ μ (fmap (fmap f) x)

  -- Derived operations

  -- Bind
  _>>=_ : M A → (A → M B) → M B
  m >>= f = μ (fmap f m)

  -- Kleisli composition
  _>=>_ : (A → M B) → (B → M C) → A → M C
  f >=> g = λ a → f a >>= g
