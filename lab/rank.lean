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

-- instance (p q : V) : Module.Finite (R := K) (M := span K {p, q}) :=
-- ⟨
-- by
-- unfold FG
-- use {p, q}
-- done
-- ⟩

theorem abp_rank_le_span_rank (a b p q : V)
(pq_diff : p ≠ q)
(abp_indep : LinearIndependent K ![a, b, p])
(a_span_pq : a ∈ span K {p, q})
(b_span_pq : b ∈ span K {p, q}) :
(card {a, b, p}) ≤ finrank K (span K {p, q}) := by
apply finset_card_le_finrank (R := K) (M := (span K {p, q})) {a, b, p}
-- failed to synthesize instance
--   Module.Finite K ↥(span K {p, q})
