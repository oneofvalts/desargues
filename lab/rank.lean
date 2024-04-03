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

theorem pq_subspace_finite (p q : V) :
    Module.Finite K (Submodule.span K {p, q}) := by
  exact Module.Finite.span_of_finite K (Set.toFinite {p, q})

theorem abp_card_le_span_rank
    (a b p q : V)
    (finite_submodule_instance := pq_subspace_finite (K := K) (V := V) p q)
    (pq_neq : p ≠ q)
    (abp_indep : LinearIndependent K ![a, b, p])
    (a_span_pq : a ∈ (span K {p, q}))
    (b_span_pq : b ∈ (span K {p, q})) :
    (card {a, b, p}) ≤ finrank K (span K {p, q}) := by
  apply finset_card_le_finrank (R := K) (M := (span K {p, q})) {a, b, p}
  -- tactic 'apply' failed, failed to unify
  --   ?m.9988.card ≤ finrank K ↥(span K {p, q})
  -- with
  --   {a, b, p}.card ≤ finrank K ↥(span K {p, q})
