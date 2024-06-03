{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Trajectories
------------------------------------------------------------------------

open import SDP.SDP
open import Monad

module SDP.Trajectory
  {M} {isMonad : Monad M}
  (sdp : SDP isMonad)
  where

open SDP sdp

open import SDP.Policy sdp

open import Function.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.String.Base hiding (head)

private variable
  t n : ℕ

-- Trajectories

data Trj (t : ℕ) : (n : ℕ) → Set where
  [_] : (x : State t) → Trj t 1
  _∷_ : (xy : Σ (State t) Ctrl) → (xys : Trj (suc t) (suc n)) → Trj t (suc (suc n))

-- Computing possible trajectories

trj : PolicySeq t n → State t → M (Trj t (suc n))
trj [] x = η [ x ]
trj (p ∷ ps) x =
  let y = p x
      mx′ = next x y
  in  fmap ((x , y) ∷_) (mx′ >>= trj ps)

-- The head of a trajectory

head : Trj t n → State t
head [ x ] = x
head ((x , _) ∷ _) = x

-- Computing values

sumTrj : Trj t n → Val
sumTrj [ x ] = 𝟘
sumTrj ((x , y) ∷ tr) = reward x y (head tr) ⊕ sumTrj tr

-- An alternative way of computing values from policy sequences, using trajectories

val′ : PolicySeq t n → State t → Val
val′ ps = measure ∘ fmap sumTrj ∘ trj ps

module Show
  (showState : ∀ {t} → State t → String)
  (showCtrl : ∀ {t} {x : State t} → Ctrl x → String)
  where

  showTrj : Trj t n → String
  showTrj [ x ] = showState x
  showTrj ((x , y) ∷ t) = showState x ++ " →⟨ " ++ showCtrl y ++ " ⟩ " ++ showTrj t
