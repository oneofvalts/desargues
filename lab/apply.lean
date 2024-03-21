import Mathlib.LinearAlgebra.LinearIndependent

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem lin_dep_aab (a b : V) : ¬ LinearIndependent K ![a, a, b] := by
intro aab_dep
rw [linearIndependent_iff'] at aab_dep
have aab_comb : (Finset.sum {0, 1, 2} fun i ↦ ![1, -1, 0] i • ![a, a, b] i) = 0 := by simp
apply (aab_dep {0, 1, 2} ![1, -1, 0]) at aab_comb
