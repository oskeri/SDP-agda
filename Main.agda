module Main where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Data.Nat.Show as ℕS
open import Data.Nat.Base
open import Data.Product.Base hiding (map)
open import Data.List.Base using (List; _∷_; []; length; map)
open import Data.String.Base using (String; _++_)
open import Function.Base
open import Agda.Builtin.Maybe
open import Data.Fin.Base

open import Monad
open import Monad.SP

import Examples.RandomWalk as RW
import Examples.GenerationDilemma as GD
import Examples.CarCrash as CC

private variable
  A B : Set

postulate
  putStrLn : String → IO ⊤
  getArgs : IO (List String)
  _>>=_ : IO A → (A → IO B) → IO B
  _>>_ : IO A → IO B → IO B
  unlines : List String → String

{-# FOREIGN GHC import Data.Text (pack, unlines) #-}
{-# FOREIGN GHC import Data.Text.IO #-}
{-# FOREIGN GHC import System.Environment #-}
{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}
{-# COMPILE GHC getArgs = fmap (map Data.Text.pack) System.Environment.getArgs #-}
{-# COMPILE GHC _>>=_ = \ _ _ -> (>>=) #-}
{-# COMPILE GHC _>>_ = \ _ _ -> (>>) #-}
{-# COMPILE GHC unlines = Data.Text.unlines #-}

die : IO ⊤
die = putStrLn "Illegal arguments"

runRW : (t n : ℕ) → IO ⊤
runRW t n = do
  let trjs = optTrjs zero
  let trjs′ = map RW.showTrj trjs
  putStrLn ("There are " ++ ℕS.show (length trjs) ++ " optimal trajectories starting from 0:")
  putStrLn (unlines trjs′)
  where
  open RW.Solution t n

runGD+ : (t n α β : ℕ) → IO ⊤
runGD+ t n α β = do
  let trjs = optTrjs
  let trjs′ = fmap showTrj trjs
  putStrLn ("There are " ++ ℕS.show (length trjs) ++ " optimal trajectories starting from GU:")
  putStrLn (showSP trjs′)
  where
  open GD.GD-+ t n α β
  open Monad.Monad SP-monad


runCC : (t n : ℕ) → IO ⊤
runCC t n = do
  let trjs = optTrjs CC.initial
  let trjs′ = map CC.showTrj trjs
  putStrLn ("There are " ++ ℕS.show (length trjs) ++ " optimal trajectories starting from the initial state:")
  putStrLn (unlines trjs′)
  where
  open CC.Solution t n


runGD+½ : (t n α β : ℕ) → IO ⊤
runGD+½ t n α β = do
  let trjs = optTrjs
  let trjs′ = fmap showTrj trjs
  putStrLn ("There are " ++ ℕS.show (length trjs) ++ " optimal trajectories starting from GU:")
  putStrLn (showSP trjs′)
  where
  open GD.GD-+½ t n α β
  open Monad.Monad SP-monad

main : IO ⊤
main = do
  xs ← getArgs
  case xs of λ where
    ("rw" ∷ t ∷ n ∷ []) → do
      case (readMaybe 10 t , readMaybe 10 n) of λ where
        (just t′ , just n′) → runRW t′ n′
        _ → die
    ("gd+" ∷ t ∷ n ∷ α ∷ β ∷ []) → do
      case (readMaybe 10 t , readMaybe 10 n , readMaybe 10 α , readMaybe 10 β) of λ where
        (just t′ , just n′ , just α′ , just β′) → runGD+ t′ n′ α′ β′
        _ → die
    ("gd+½" ∷ t ∷ n ∷ α ∷ β ∷ []) → do
      case (readMaybe 10 t , readMaybe 10 n , readMaybe 10 α , readMaybe 10 β) of λ where
        (just t′ , just n′ , just α′ , just β′) → runGD+½ t′ n′ α′ β′
        _ → die
    ("cc" ∷ t ∷ n ∷ []) → do
      case (readMaybe 10 t , readMaybe 10 n) of λ where
        (just t′ , just n′) → runCC t′ n′
        _ → die
    _ → die
