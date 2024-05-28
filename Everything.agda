-- A small library for solving sequential decision problems in Agda

-- Utility modules

import Monad
import Finite
import Max

-- Some monad instances

import Monad.Identity
import Monad.List

-- Definition and properties of SDP:s

import Value
import SDP.SDP
import SDP.Policy
import SDP.Trajectory
import SDP.BellmanEq
