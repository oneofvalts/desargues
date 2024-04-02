import Mathlib.RingTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional

open Finset Submodule FiniteDimensional LinearIndependent

variable [DivisionRing K] [AddCommGroup V] [Module K V] [DecidableEq V]

theorem pq_span_dim_ineq
(p q : V)
(pq_neq : p ≠ q) :
Set.finrank (R := K) (toSet {p, q}) ≤ 2 := by
have pq_card : (card {p, q}) = 2 := by aesop
rw [<- pq_card]
apply finrank_span_finset_le_card {p, q}

theorem pq_finite
(p q : V) :
Set.Finite {p, q} := by
aesop

theorem pq_subspace_finite
(p q : V) :
Module.Finite K (span K {p, q}) := by
apply Module.Finite.span_of_finite
aesop -- proves Set.Finite {p,q}

theorem abp_rank_le_span_rank
(a b p q : V)
(pq_neq : p ≠ q)
(abp_indep : LinearIndependent K ![a, b, p])
(a_span_pq : a ∈ (span K {p, q}))
(b_span_pq : b ∈ (span K {p, q})) :
(card ({a, b, p} : Finset (span K {p, q}))) ≤ finrank K (span K {p, q}) := by
apply finset_card_le_finrank (R := K) (M := M) {a, b, p}
-- overloaded, errors
--   failed to synthesize instance
--     Singleton V (Finset ↥(span K ↑{p, q}))
--
--   28:2 'a' is not a field of structure 'Finset'
