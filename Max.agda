------------------------------------------------------------------------
-- Computing the maximum value of a function given a vector of arguments
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

module Max
  {V : Set} {_≤_ : V → V → Set}
  (V-preorder : IsTotalPreorder _≡_ _≤_)
  where

open import Data.Nat.Base hiding (_≤_)
open import Data.Vec.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Function.Base
open import Data.Fin.Base hiding (_≤_)

open IsTotalPreorder V-preorder
  using (total)
  renaming (refl to ≤-refl; trans to ≤-trans)

private variable
  A : Set
  n : ℕ

-- Computing the maximum value (and the corresponding argument) of a function
-- from a list of arguments

max′ : (f : A → V) → Vec A (suc n) → A × V
max′ f (a ∷ []) = a , f a
max′ f (a ∷ a′ ∷ as) =
  case total (f a) (f a′) of λ where
    (inj₁ _) → max′ f (a′ ∷ as)
    (inj₂ _) → max′ f (a ∷ as)

-- Computing the maximum value of a function from a list of arguments

max : (f : A → V) → Vec A (suc n) → V
max f as = proj₂ (max′ f as)

-- Computing which argument gives the maximum value of a function
-- from a list of arguments

argmax : (f : A → V) → Vec A (suc n) → A
argmax f as = proj₁ (max′ f as)

-- The maximum argument given by argmax gives the maximum value as given by max

max-argmax : (f : A → V) → (as : Vec A (suc n)) → max f as ≡ f (argmax f as)
max-argmax f (a ∷ []) = refl
max-argmax f (a ∷ a′ ∷ as)
  with IsTotalPreorder.total V-preorder (f a) (f a′)
… | inj₁ x = max-argmax f (a′ ∷ as)
… | inj₂ y = max-argmax f (a ∷ as)

-- The value given by max is the highest value

≤-max : (f : A → V) (as : Vec A (suc n)) (x : Fin (suc n))
      → f (lookup as x) ≤ max f as
≤-max f (a ∷ []) zero = ≤-refl
≤-max f (a ∷ a′ ∷ as) n with total (f a) (f a′)
≤-max f (a ∷ a′ ∷ as) zero | inj₁ fa≤fa′ = ≤-trans fa≤fa′ (≤-max f (a′ ∷ as) zero)
≤-max f (a ∷ a′ ∷ as) (suc n) | inj₁ _ = ≤-max f (a′ ∷ as) n
≤-max f (a ∷ a′ ∷ as) zero | inj₂ _ = ≤-max f (a ∷ as) zero
≤-max f (a ∷ a′ ∷ as) (suc zero) | inj₂ fa′≤fa = ≤-trans fa′≤fa (≤-max f (a ∷ as) zero)
≤-max f (a ∷ a′ ∷ as) (suc (suc n)) | inj₂ _ = ≤-max f (a ∷ as) (suc n)
