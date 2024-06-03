{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- The random walk SDP
------------------------------------------------------------------------

module Examples.RandomWalk where

open import Function.Base
open import Data.Fin.Base hiding (_≤_)
open import Data.Fin.Show
open import Data.List.Base hiding ([_])
open import Data.Maybe.Base hiding (map)
open import Data.Nat.Base hiding (_≤_)
open import Data.Unit.Base
open import Data.Product.Base hiding (map)
open import Agda.Builtin.Equality
open import Data.String.Base hiding (_≤_; length; head; show)

open import Finite
open import Monad.List
open import Value.Nat
open import SDP.SDP

open Value ℕ-value

private variable
  t n : ℕ
  A : Set

-- This is perhaps not a very interesting example since there
-- is no decision to be made

randomWalkSDP : SDP listMonad
randomWalkSDP = record
  { State = State
  ; Ctrl = λ _ → ⊤
  ; next = λ x _ → next x
  ; value = ℕ-value
  ; reward = λ _ _ → reward
  -- Taking the sum of the rewards for each possible next step
  -- might not make much sense, but it also doesn't really matter.
  ; measure = sum
  ; measure-mono = sum-mon
  }
  where

  State : ℕ → Set
  State n = Fin (suc n)

  next : (x : State t) → List (State (suc t))
  next zero = zero ∷ suc zero ∷ []
  next (suc x) = inject₁ (inject₁ x) ∷ inject₁ (suc x) ∷ suc (suc x) ∷ []

  -- The reward is the (number corresponding to) a state

  reward : State t → ℕ
  reward x = toℕ x

  sum-mon : {f g : A → ℕ}
          → ((a : A) → f a ≤ g a)
          → (xs : List A)
          → sum (map f xs) ≤ sum (map g xs)
  sum-mon f≤g [] = ≤-refl
  sum-mon f≤g (x ∷ xs) = ⊕-mono (f≤g x) (sum-mon f≤g xs)

randomWalkFiniteSDP : Finite-SDP listMonad
randomWalkFiniteSDP = record
  { sdp = randomWalkSDP
  ; Ctrl-finite = λ _ → _ , ⊤-finite
  }

open import SDP.Finite randomWalkFiniteSDP
open import SDP.Policy randomWalkSDP
open import SDP.Trajectory randomWalkSDP hiding (head)
open import SDP.BackwardsInduction randomWalkSDP isOptExtFun

showTrj : Trj t n → String
showTrj = Show.showTrj show (λ _ → "_")

-- Solve the Random walk SDP for a given time and steps

module Solution (t n : ℕ) where

  -- The optimal policy sequence starting at time t, going n steps

  optPs : PolicySeq t n
  optPs = bi t n

  -- The trajectories of optPs

  optTrjs : _ → List (Trj t (suc n))
  optTrjs x = trj optPs x

-- Solve the Random walk SDP for time 0 and 3 steps

module Solution₀₃ where

  open Solution 0 3 public

  -- The optimal policy sequence is the one always taking the only option

  optPs≡ : optPs ≡ const tt ∷ const tt ∷ const tt ∷ []
  optPs≡ = refl

  val-optPs : val optPs zero ≡ 19
  val-optPs = refl

  trjs : List (Trj 0 4)
  trjs = optTrjs zero

  -- There are 13 trajectories (as expected)

  trjs13 : length trjs ≡ 13
  trjs13 = refl

  -- Inspection shows that the trajectories are the expected ones
  -- In particular, the first trajectory is the one that stays in zero...

  trjs-head : head trjs ≡ just ((zero , _) ∷ (zero , _) ∷ (zero , _) ∷ [ zero ])
  trjs-head = refl

  -- ... and the last trajectory is the one that always moves one step up
  trjs-last : last trjs ≡ just ((zero , _) ∷ (suc zero , _) ∷ (suc (suc zero) , _) ∷ [ suc (suc (suc zero)) ])
  trjs-last = refl
