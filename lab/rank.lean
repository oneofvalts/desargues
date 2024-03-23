import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.Finset.Basic

open Finset Set Submodule FiniteDimensional

variable [DivisionRing K] [AddCommGroup V] [Module K V] -- [DecidableEq V] [StrongRankCondition K]

variable (p q : V)
def a : Finset V := (toFinset {p})

-- #print toSet

-- theorem pq_span_dim_ineq (p q : V) : finrank K ({p, q}) ≤ 2 := by apply finrank_span_finset_le_card (toFinset {p, q})
