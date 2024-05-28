------------------------------------------------------------------------
-- The simple probability monad
------------------------------------------------------------------------

module Monad.SP where

open import Monad

open import Function.Base
open import Data.List.Base
open import Data.List.Properties
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base hiding (map)
open import Relation.Binary.PropositionalEquality
  hiding ([_])

open ≡-Reasoning

private variable
  A B C : Set
  f g : A → B

-- Probabilities are represented as "weights" (natural numbers)
-- The corresponding probability of an entry with weight w is given by
-- w divided by the sum of all weights.

SP : Set → Set
SP A = List (ℕ × A)

-- The total weight

totalWeight : SP A → ℕ
totalWeight [] = 0
totalWeight ((w , _) ∷ xs) = w + totalWeight xs

-- Scale all the weights

scaleWeights : ℕ → SP A → SP A
scaleWeights w xs = map (λ (w′ , x) → w * w′ , x) xs

-- Some properties of the scaling function

scale-scale : (w w′ : ℕ) (xs : SP A)
            → scaleWeights w (scaleWeights w′ xs) ≡ scaleWeights (w * w′) xs
scale-scale w w′ [] = refl
scale-scale w w′ (x ∷ xs) =
  cong₂ (_∷_)
    (cong (_, proj₂ x) (sym (*-assoc w w′ _)))
    (scale-scale w w′ xs)

scale-++ : (w : ℕ) (xs ys : SP A)
         → scaleWeights w (xs ++ ys) ≡ scaleWeights w xs ++ scaleWeights w ys
scale-++ w [] ys = refl
scale-++ w (x ∷ xs) ys = cong (_ ∷_) (scale-++ w xs ys)

private
  apᵣ : (f : A → B) → ℕ × A → ℕ × B
  apᵣ f (w , a) = w , f a

-- SP is a functor

SP-functor : Functor SP
SP-functor = record
  { fmap = fmap
  ; fmap-id = fmap-id
  ; fmap-∘ = fmap-∘
  }
  where
  fmap : (A → B) → SP A → SP B
  fmap f xs = map (apᵣ f) xs

  fmap-id : (xs : SP A) → fmap id xs ≡ xs
  fmap-id [] = refl
  fmap-id (x ∷ xs) = cong (_ ∷_) (fmap-id xs)

  fmap-∘ : (xs : SP A) → fmap (f ∘ g) xs ≡ fmap f (fmap g xs)
  fmap-∘ [] = refl
  fmap-∘ (x ∷ xs) = cong (_ ∷_) (fmap-∘ xs)

-- fmap distributes over ++

fmap-++ : (xs ys : SP A)
        → let open Functor SP-functor
          in fmap f (xs ++ ys) ≡ fmap f xs ++ fmap f ys
fmap-++ [] ys = refl
fmap-++ (x ∷ xs) ys = cong (_ ∷_) (fmap-++ xs ys)

-- scaleWeights commutes with fmap

scale-fmap : (w : ℕ) (xs : SP A)
           → let open Functor SP-functor
             in  scaleWeights w (fmap f xs) ≡ fmap f (scaleWeights w xs)
scale-fmap w [] = refl
scale-fmap w (x ∷ xs) = cong (_ ∷_) (scale-fmap w xs)

-- SP is a monad

SP-monad : Monad SP
SP-monad = record
  { functor = SP-functor
  ; η = η
  ; μ = μ
  ; μ∘η = μ∘η
  ; μ∘mapη = μ∘mapη
  ; μ∘μ = μ∘μ
  ; map∘η = map∘η
  ; map∘μ = map∘μ
  }
  where
  open Functor SP-functor
  η : A → SP A
  η x = [ 1 , x ]

  μ : SP (SP A) → SP A
  μ [] = []
  μ ((w , xs) ∷ xss) = scaleWeights w xs ++ μ xss

  μ∘η : (xs : SP A) → μ (η xs) ≡ xs
  μ∘η xs = begin
    map (λ x → proj₁ x + 0 , proj₂ x) xs ++ [] ≡⟨ ++-identityʳ _ ⟩
    map (λ x → proj₁ x + 0 , proj₂ x) xs       ≡⟨ map-cong (λ _ → cong (_, _) (+-identityʳ _)) xs ⟩
    map (λ x → proj₁ x , proj₂ x) xs           ≡⟨⟩
    map id xs                                  ≡⟨ map-id xs ⟩
    xs                                         ∎

  μ∘mapη : (xs : SP A) → μ (fmap η xs) ≡ xs
  μ∘mapη [] = refl
  μ∘mapη (x ∷ xs) = cong₂ _∷_ (cong (_, _) (*-identityʳ _)) (μ∘mapη xs)

  μ++ : (xs ys : SP (SP A)) → μ (xs ++ ys) ≡ μ xs ++ μ ys
  μ++ [] ys = refl
  μ++ ((w , x) ∷ xs) ys = begin
    scaleWeights w x ++ μ (xs ++ ys)   ≡⟨ cong (_ ++_) (μ++ xs ys) ⟩
    scaleWeights w x ++ μ xs ++ μ ys   ≡˘⟨ ++-assoc _ (μ xs) (μ ys) ⟩
    (scaleWeights w x ++ μ xs) ++ μ ys ∎

  scale-μ : (w : ℕ) (xss : SP (SP A)) → μ (scaleWeights w xss) ≡ scaleWeights w (μ xss)
  scale-μ w [] = refl
  scale-μ w ((w′ , xs) ∷ xss) = begin
    scaleWeights (w * w′) xs ++ μ (scaleWeights w xss)
      ≡⟨ cong₂ _++_ (sym (scale-scale w w′ xs)) (scale-μ w xss) ⟩
    scaleWeights w (scaleWeights w′ xs) ++ scaleWeights w (μ xss)
      ≡˘⟨ scale-++ w (scaleWeights w′ xs) (μ xss) ⟩
    scaleWeights w (scaleWeights w′ xs ++ μ xss) ∎

  μ∘μ : (xsss : SP (SP (SP A))) → μ (μ xsss) ≡ μ (fmap μ xsss)
  μ∘μ [] = refl
  μ∘μ ((w , xs) ∷ xss) = begin
    μ (scaleWeights w xs ++ μ xss)          ≡⟨ μ++ (scaleWeights w xs) (μ xss) ⟩
    μ (scaleWeights w xs) ++ μ (μ xss)      ≡⟨ cong₂ _++_ (scale-μ w xs) (μ∘μ xss) ⟩
    scaleWeights w (μ xs) ++ μ (fmap μ xss) ∎

  map∘η : (f : A → B) (x : A) → fmap f (η x) ≡ η (f x)
  map∘η f x = refl

  map∘μ : (f : A → B) (xss : SP (SP A)) → fmap f (μ xss) ≡ μ (fmap (fmap f) xss)
  map∘μ f [] = refl
  map∘μ f ((w , xs) ∷ xss) = begin
    fmap f (scaleWeights w xs ++ μ xss)
      ≡⟨ fmap-++ (scaleWeights w xs) (μ xss) ⟩
    fmap f (scaleWeights w xs) ++ fmap f (μ xss)
      ≡⟨ cong₂ _++_ (sym (scale-fmap w xs)) (map∘μ f xss) ⟩
    scaleWeights w (fmap f xs) ++ μ (fmap (fmap f) xss) ∎
