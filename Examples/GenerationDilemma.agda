------------------------------------------------------------------------
-- The generation dilemma SDP
------------------------------------------------------------------------

module Examples.GenerationDilemma where

open import Data.Fin.Base using (zero; suc)
open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Integer.Base using (-[1+_])
open import Data.List.Base
open import Data.Product.Base
open import Data.Rational.Base hiding (_≤_)
open import Data.String.Base hiding (_≤_)
open import Data.Unit.Base
open import Agda.Builtin.Equality

open import Value.Rational

open import SDP.SDP
open import Monad.SP
open import Monad
open import Finite

open Monad.Monad SP-monad

private variable
  t n : ℕ

data State : ℕ → Set where
  GU : State t
  B BT : State (suc t)
  GS : State (suc (suc t))

data Ctrl-GU : Set where
  a b : Ctrl-GU

Ctrl : State t → Set
Ctrl GU = Ctrl-GU
Ctrl B = ⊤
Ctrl BT = ⊤
Ctrl GS = ⊤

-- Parameters and requirements of the SDP given a Value type

record GD-params (V : Value ℚ) : Set where
  open Value V
  field
    -- Probabilities/weights of the two transitions for control 'a'
    -- α is the weight of staying in GU
    -- β is the weight of moving to B
    α β : ℕ
    -- The reward function
    reward : (x : State t) → Ctrl x → State (suc t) → ℚ

    -- * is monotone with respect to the order relation for values
    *-monoʳ-≤ : ∀ (r : ℚ) .⦃ _ : NonNegative r ⦄ {p q} → p ≤ q → p * r ≤ q * r
    *-monoˡ-≤ : ∀ (r : ℚ) .⦃ _ : NonNegative r ⦄ {p q} → p ≤ q → r * p ≤ r * q


  next : (x : State t) → Ctrl x → SP (State (suc t))
  next GU a  = (α , GU) ∷ (β , B) ∷ []
  next GU b  = η BT
  next B tt  = η B
  next BT tt = η GS
  next GS tt = η GS

-- The generation dilemma as an SDP, given some parameters,
-- using expectation value as measure

generationDilemmaSDP : (v : Value ℚ) → GD-params v → SDP SP-monad
generationDilemmaSDP v p = record
  { State = State
  ; Ctrl = Ctrl
  ; next = next
  ; value = v
  ; reward = reward
  ; measure = ev
  ; measure-mono = ev-mono
  }
  where
  open GD-params p
  open ℚ-EV v *-monoʳ-≤ *-monoˡ-≤
  open EV v ev-helper ev-helper-mono

generationDilemmaFSDP : (v : Value ℚ) → GD-params v → Finite-SDP SP-monad
generationDilemmaFSDP v p = record
  { sdp = generationDilemmaSDP v p
  ; Ctrl-finite = λ where
      GU → _ , fin-Ctrl-GU
      B → _ , ⊤-finite
      BT → _ , ⊤-finite
      GS → _ , ⊤-finite
  }
  where
  fin-Ctrl-GU : Finite 2 Ctrl-GU
  fin-Ctrl-GU = record
    { toFin = λ { a → zero ; b → suc zero}
    ; fromFin = λ { zero → a ; (suc zero) → b}
    ; to∘from = λ { zero → refl ; (suc zero) → refl}
    ; from∘to = λ { a → refl ; b → refl}
    }

-- Showing

showState : State t → String
showState GU = "GU"
showState B = "B "
showState BT = "BT"
showState GS = "GS"

showCtrl : {x : State t} → Ctrl x → String
showCtrl {x = GU} a = "a"
showCtrl {x = GU} b = "b"
showCtrl {x = B} tt = "_"
showCtrl {x = BT} tt = "_"
showCtrl {x = GS} tt = "_"

-- Solving the Generation dilemma SDP at some time and number of
-- steps given weights α and β adding the rewards of each generation.

module GD-+ (t n α β : ℕ) where

  -- The reward is only given by the current state

  reward : ∀ {t} → State t → ℚ
  reward GU = 1ℚ
  reward B  = -[1+ 9 ] / 1
  reward BT = -[1+ 9 ] / 1
  reward GS = 1ℚ

  open import Data.Rational.Properties

  params : GD-params ℚ-value-+
  params = record
    { α = α
    ; β = β
    ; reward = λ x y x′ → reward x′
    ; *-monoʳ-≤ = *-monoʳ-≤-nonNeg
    ; *-monoˡ-≤ = *-monoˡ-≤-nonNeg
    }

  fsdp : Finite-SDP SP-monad
  fsdp = generationDilemmaFSDP _ params

  open Finite-SDP fsdp

  open import SDP.Policy sdp
  open import SDP.Trajectory sdp
  open import SDP.Finite fsdp
  open import SDP.BackwardsInduction sdp isOptExtFun

  -- Showing trajectories

  showTrj : ∀ {t n} → Trj t n → String
  showTrj = Show.showTrj showState showCtrl

  optPs : PolicySeq t n
  optPs = bi t n

  optTrjs : SP (Trj t (suc n))
  optTrjs = sortHighest (trj optPs GU)
