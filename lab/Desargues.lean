import Mathlib.LinearAlgebra.Projectivization.Basic

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem lindep_imp_span (a b c : V) : a ≠ 0 → b ≠ 0 → c ≠ 0 → ¬ LinearIndependent K ![a, b, c] →
a ∈ Submodule.span K {b, c} := by sorry
