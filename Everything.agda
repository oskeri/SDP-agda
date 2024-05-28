------------------------------------------------------------------------
-- A small library for solving sequential decision problems in Agda
------------------------------------------------------------------------

-- Utility modules

import Monad
import Finite
import Max
import Value

-- Some monad instances

import Monad.Identity
import Monad.List

-- Some value isntances

import Value.Nat
import Value.Int
import Value.Rational

-- Definition and properties of SDP:s

import SDP.SDP
import SDP.Policy
import SDP.Trajectory
import SDP.BellmanEq
import SDP.Finite
import SDP.BackwardsInduction
