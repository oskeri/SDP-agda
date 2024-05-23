open import SDP.SDP
open import Monad

module SDP.Trajectory {M} {isMonad : Monad M} (sdp : SDP isMonad) where

open SDP sdp

open import SDP.Policy sdp

open import Function.Base
open import Data.Nat.Base
open import Data.Product.Base

private variable
  t n : ℕ


-- Trajectories

data Trj (t : ℕ) : (n : ℕ) → Set where
  [_] : (x : X t) → Trj t 1
  _∷_ : (xy : Σ (X t) Y) → (xys : Trj (suc t) (suc n)) → Trj t (suc (suc n))

-- Computing possible trajectories

trj : PolicySeq t n → X t → M (Trj t (suc n))
trj [] x = η [ x ]
trj (p ∷ ps) x =
  let y = p x
      mx′ = next x y
  in  fmap ((x , y) ∷_) (mx′ >>= trj ps)

-- The head of a trajectory

head : Trj t n → X t
head [ x ] = x
head ((x , _) ∷ _) = x

-- Computing values

sumTrj : Trj t n → Val
sumTrj [ x ] = 𝟘
sumTrj ((x , y) ∷ tr) = reward x y (head tr) ⊕ sumTrj tr

-- An alternative way of computing values from policy sequences, using trajectories

val′ : PolicySeq t n → X t → Val
val′ ps = measure ∘ fmap sumTrj ∘ trj ps
