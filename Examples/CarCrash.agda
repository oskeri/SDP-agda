module Examples.CarCrash where

open import Data.Nat.Base hiding (_+_; _≤_)
open import Data.Product.Base

open import Monad
open import Monad.List
open import SDP.SDP
open import Value.Int
open import Value

open import Data.Fin.Base hiding (_+_; _≤_)
open import Data.List.Base hiding (_++_; [_])
open import Data.String.Base hiding (_≤_; length; head)
open import Data.Integer.Base hiding (suc)
open import Data.Integer.Properties
open import Agda.Builtin.Equality
open import Agda.Builtin.Maybe

open Monad.Monad listMonad

private variable
  t n : ℕ

data Baby : (t : ℕ) → Set where
  unsafe : Baby t
  safe : Baby (suc t)

↑Baby : Baby t → Baby (suc t)
↑Baby unsafe = unsafe
↑Baby safe = safe

data Help : (t : ℕ) → Set where
  nohelp : Help t
  help : Help (suc t)

↑Help : Help t → Help (suc t)
↑Help nohelp = nohelp
↑Help help = help

private variable
  b : Baby _
  h : Help _

-- The state represents whether the baby is safe or not and whether help is comming.

State : (t : ℕ) → Set
State t = Baby t × Help t

initial : State t
initial = unsafe , nohelp

↑State : State t → State (suc t)
↑State (b , h) = ↑Baby b , ↑Help h

data Ctrl : State t → Set where
  callForHelp : Ctrl (b , nohelp)
  saveBaby : Ctrl (unsafe , h)
  doNothing : Ctrl (b , h)

next : (x : State t) (y : Ctrl x) → List (State (suc t))
next (b , .nohelp) callForHelp = η (↑Baby b , help)
-- Trying to save the baby at time 0 always succeeds
next {(zero)} (.unsafe , h) saveBaby = η (safe , ↑Help h)
-- Trying to save the baby at time 1 succeeds 50% of the time
next {suc zero} (.unsafe , h) saveBaby =
  (safe , ↑Help h) ∷ (unsafe , ↑Help h) ∷ []
-- Trying to save the baby at time 2 or later always fails
next {suc (suc t)} (.unsafe , h) saveBaby = η (unsafe , ↑Help h)
next x doNothing = η (↑State x)

-- The reward is only given by whether the baby is safe or not in the next state.

reward : (x : State (suc t)) → ℤ
reward (unsafe , h) = -[1+ 9 ] -- -10
reward (safe , h) = 1ℤ         -- +1

carCrash-SDP : SDP listMonad
carCrash-SDP = record
  { State = State
  ; Ctrl = Ctrl
  ; next = next
  ; value = ℤ-valueʳ
  ; reward = λ _ _ → reward
  ; measure = foldr _+_ 0ℤ
  ; measure-mono = measure-mono
  }
  where
  -- Maybe the average would have been a more interesting measure function.
  measure-mono : {A : Set} {f g : A → ℤ}
               → (∀ x → f x ≤ g x) → (xs : List A)
               → foldr _+_ 0ℤ (fmap f xs) ≤ foldr _+_ 0ℤ (fmap g xs)
  measure-mono f≤g [] = ≤-refl
  measure-mono f≤g (x ∷ xs) = +-mono-≤ (f≤g x) (measure-mono f≤g xs)

carCrash-fSDP : Finite-SDP listMonad
carCrash-fSDP = record
  { sdp = carCrash-SDP
  ; Ctrl-finite = λ where
      (unsafe , nohelp) → 2 , record
        { toFin   = λ { callForHelp → zero ; saveBaby → suc zero ; doNothing → suc (suc zero)}
        ; fromFin = λ { zero → callForHelp ; (suc zero) → saveBaby ; (suc (suc zero)) → doNothing}
        ; to∘from = λ { zero → refl ; (suc zero) → refl ; (suc (suc zero)) → refl}
        ; from∘to = λ { callForHelp → refl ; saveBaby → refl ; doNothing → refl}
        }
      (unsafe , help) → 1 , record
        { toFin = λ { saveBaby → zero ; doNothing → suc zero}
        ; fromFin = λ { zero → saveBaby ; (suc zero) → doNothing}
        ; to∘from = λ { zero → refl ; (suc zero) → refl}
        ; from∘to = λ { saveBaby → refl ; doNothing → refl}
        }
      (safe , nohelp) → 1 , record
        { toFin = λ { callForHelp → zero ; doNothing → suc zero}
        ; fromFin = λ { zero → callForHelp ; (suc zero) → doNothing}
        ; to∘from = λ { zero → refl ; (suc zero) → refl}
        ; from∘to = λ { callForHelp → refl ; doNothing → refl}
        }
      (safe , help) → 0 , record
        { toFin = λ { doNothing → zero}
        ; fromFin = λ { zero → doNothing}
        ; to∘from = λ { zero → refl}
        ; from∘to = λ { doNothing → refl}
        }
  }

open import SDP.Finite carCrash-fSDP
open import SDP.Policy carCrash-SDP
open import SDP.Trajectory carCrash-SDP hiding (head)
open import SDP.BackwardsInduction carCrash-SDP isOptExtFun

showBaby : Baby t → String
showBaby unsafe = "×"
showBaby safe = "✓"

showHelp : Help t → String
showHelp nohelp = "×"
showHelp help = "✓"

showState : State t → String
showState (b , h) = "(B: " ++ showBaby b ++ ", H: " ++ showHelp h ++ ")"

showCtrl : {x : State t} → Ctrl x → String
showCtrl callForHelp = "call"
showCtrl saveBaby = "save"
showCtrl doNothing = "wait"

-- Showing trajectories

showTrj : Trj t n → String
showTrj = Show.showTrj showState showCtrl

-- Solve the Car crash SDP for a given time and steps

module Solution (t n : ℕ) where

  -- The optimal policy sequence starting at time t, going n steps

  optPs : PolicySeq t n
  optPs = bi t n

  -- The trajectories of optPs

  optTrjs : _ → List (Trj t (suc n))
  optTrjs x = trj optPs x

-- Solve the Car crash SDP for three steps starting at time 0

module Solution₀₃ where

  open Solution 0 3 public

  -- The value of the optimal policy is 1
  -- This means that the baby was saved

  val-optPs : val optPs initial ≡ 1ℤ
  val-optPs = refl

  trjs : List (Trj 0 4)
  trjs = optTrjs initial

  -- There is 1 optimal trajectory (as expected)

  trjs1 : length trjs ≡ 1
  trjs1 = refl

  -- Inspection shows that the trajectory is:
  -- "save -> wait -> wait"

  trj′ : head trjs ≡ just ((initial , saveBaby) ∷
                          ((safe , nohelp) , doNothing) ∷
                          ((safe , nohelp) , doNothing) ∷
                          [ safe , nohelp ])
  trj′ = refl
