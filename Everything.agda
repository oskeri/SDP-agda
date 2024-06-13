------------------------------------------------------------------------
-- A small library for solving sequential decision problems in Agda
------------------------------------------------------------------------

-- Utility modules
------------------

-- Definitions of functors and monads
import Monad

-- Definitions of finite types
import Finite

-- Computing the maximum value of a function
import Max

-- Some monad instances
-----------------------

import Monad.Identity
import Monad.List
import Monad.SP

-- Definition and properties of SDP:s
-------------------------------------

-- Values
import Value
-- Definition of an SDP (States/Controls etc.)
import SDP.SDP
-- Policies and policy sequences
import SDP.Policy
-- Trajectories
import SDP.Trajectory
-- A proof of (a special case of) Bellman's equation
import SDP.BellmanEq
-- Finding optimal policy sequence extensions for finite SDP:s
import SDP.Finite
-- Solving an SDP using backwards induction
import SDP.BackwardsInduction

-- Some value instances
-----------------------

import Value.Nat
import Value.Int
import Value.Rational

-- Examples
-----------

import Examples.RandomWalk
import Examples.GenerationDilemma
import Examples.CarCrash

-- A main module that can be compiled to run the examples
---------------------------------------------------------

import Main
