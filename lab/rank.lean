import Mathlib.LinearAlgebra.FiniteDimensional

open Finset Submodule FiniteDimensional LinearIndependent

variable [DivisionRing K] [AddCommGroup V] [Module K V] [DecidableEq V]

-- variable (p q : V)
-- def a : Finset V := {p, q}

-- #print toSet
-- #print finrank
-- #print finrank_span_finset_le_card

theorem pq_span_dim_ineq (p q : V) (pq_diff : p ≠ q) : Set.finrank (R := K) (toSet {p, q}) ≤ 2 := by
have pq_card : (card {p, q}) = 2 := by aesop
rw [<- pq_card]
apply finrank_span_finset_le_card {p, q}

theorem test (p q : V) (a b : (span K ({p, q} : Finset V).toSet)) (ab_neq : a ≠ b):
({a, b} : Finset (span K ({p, q} : Finset V).toSet)).card = 2 := by aesop

theorem abp_rank_le_span_rank (p q : V)
(a b : (span K ({p, q} : Finset V).toSet)) (ab_neq : a ≠ b)
(pq_diff : p ≠ q)
(abp_indep : LinearIndependent K ![a, b]) :
-- (a_span_pq : a ∈ (span K ({p, q} : Finset V).toSet))
-- (b_span_pq : b ∈ (span K ({p, q} : Finset V).toSet)) :
({a, b} : Finset (span K ({p, q} : Finset V).toSet)).card ≤
finrank K (span K ({p, q} : Finset V).toSet) := by
set M := span K ({p, q} : Finset V).toSet
letI : FiniteDimensional K M := span_finset K {p, q}
apply finset_card_le_finrank (R := K) (M := M) {a, b}
-- overloaded, errors
--   failed to synthesize instance
--     Singleton V (Finset ↥(span K ↑{p, q}))
--
--   32:2 'a' is not a field of structure 'Finset'
