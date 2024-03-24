import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence

namespace Desargues
open Finset Set Submodule FiniteDimensional Projectivization
open scoped LinearAlgebra.Projectivization

variable [DivisionRing K] [AddCommGroup V] [Module K V] [DecidableEq V] [StrongRankCondition K]

-- def indexer_generator (X Y Z : ℙ K V) : Fin 3 → ℙ K V :=
-- fun i : Fin 3 => match i with
-- | 0 => X
-- | 1 => Y
-- | 2 => Z
--
-- def coeff_indexer (k1 k2 k3 : K) : Fin 3 → K :=
-- fun i : Fin 3 => match i with
-- | 0 => k1
-- | 1 => k2
-- | 2 => k3

class ProjectiveGeometry (point : Type u) where
ell : point → point → point → Prop
l1  : ∀ a b, ell a b a
l2  : ∀ a b p q, ell a p q → ell b p q → p ≠ q → ell a b p
l3  : ∀ a b c d p, ell p a b → ell p c d → ∃ q : point, ell q a c ∧ ell q b d

-- Lemmas for distribution of composition.
theorem rep_comp_3 (X Y Z : ℙ K V) :
Projectivization.rep ∘ ![X, Y, Z] = ![X.rep, Y.rep, Z.rep] := by
exact List.ofFn_inj.mp rfl

theorem rep_comp_2 (X Y : ℙ K V) :
Projectivization.rep ∘ ![X, Y] = ![X.rep, Y.rep] := by
exact List.ofFn_inj.mp rfl

theorem lin_dep_aab (a b : V) : ¬ LinearIndependent K ![a, a, b] := by
intro aab_dep
rw [linearIndependent_iff'] at aab_dep
specialize aab_dep {0, 1, 2} ![1, -1, 0]
aesop

theorem lin_dep_aba (a b : V) : ¬ LinearIndependent K ![a, b, a] := by
intro aab_dep
rw [linearIndependent_iff'] at aab_dep
specialize aab_dep {0, 1, 2} ![1, 0, -1]
aesop

theorem lin_dep_imp_span (a b c : V) (bc_indep : LinearIndependent K ![b, c])
(abc_dep : ¬ LinearIndependent K ![a, b, c]) : a ∈ span K {b, c} := by
rw [not_iff_not.mpr linearIndependent_fin_succ] at abc_dep
push_neg at abc_dep
simp only [Fin.isValue, Matrix.cons_val_zero] at abc_dep
convert abc_dep bc_indep
ext x
simp [show Fin.tail ![a, b, c] = ![b, c] from rfl]
rw [or_comm]

-- Version with representatives of the axiom L_2.
theorem l2_rep (a b p q : V) (apq_dep : ¬ LinearIndependent K ![a, p, q])
(bpq_dep : ¬ LinearIndependent K ![b, p, q]) (pq_indep : LinearIndependent K ![p, q]) :
¬ LinearIndependent K ![a, b, p] := by
-- p and q are not the same points.
have pq_neq : p ≠ q := by sorry
-- a,b,p,q are in the span of p,q.
have a_span_pq : a ∈ span K {p, q} := by {
apply lin_dep_imp_span a p q pq_indep apq_dep
}
have b_span_pq : b ∈ span K {p, q} := by {
apply lin_dep_imp_span b p q pq_indep bpq_dep
}
have ppq_dep : ¬ LinearIndependent K ![p, p, q] := by apply (lin_dep_aab p q)
have p_span_pq : p ∈ span K {p, q} := by {
apply lin_dep_imp_span p p q pq_indep ppq_dep
}
have qpq_dep : ¬ LinearIndependent K ![q, p, q] := by apply (lin_dep_aba q p)
have q_span_pq : q ∈ span K {p, q} := by {
apply lin_dep_imp_span q p q pq_indep qpq_dep
}
intro abp_dep
have pq_span_dim_ineq (p q : V) (pq_diff : p ≠ q) : Set.finrank (R := K) (toSet {p, q}) ≤ 2 := by {
have pq_card : (card {p, q}) = 2 := by aesop
rw [<- pq_card]
apply finrank_span_finset_le_card {p, q}
}
apply pq_span_dim_ineq at pq_neq


-- Every Projectivization is a ProjectiveGeometry
instance : ProjectiveGeometry (ℙ K V) :=
⟨
-- fun X Y Z => ∃ k1 k2 k3 : K, ¬(k1 = 0 ∧ k2 = 0 ∧ k3 = 0) ∧ k1 • X.rep + k2 • Y.rep + k3 • Z.rep = 0,
-- fun X Y Z => ¬ LinearIndependent K ![X.rep, Y.rep, Z.rep],
-- fun X Y Z => Dependent (index X Y Z),
fun X Y Z => ¬ Independent ![X, Y, Z],

by
intro A B
rw [independent_iff, rep_comp_3]
rw [not_linearIndependent_iff]
use {0, 1, 2}, ![1, 0, -1]
constructor
simp
simp
done,

by
intro A B P Q
intro ABPcollinear BPQcollinear PneqQ
rw [independent_iff, rep_comp_3] at ABPcollinear
rw [independent_iff, rep_comp_3] at BPQcollinear
rw [<- independent_pair_iff_neq] at PneqQ
rw [independent_iff, rep_comp_2] at PneqQ
rw [independent_iff, rep_comp_3]
apply l2_rep A.rep B.rep P.rep Q.rep
exact ABPcollinear
exact BPQcollinear
exact PneqQ
done,

sorry
⟩

end Desargues
