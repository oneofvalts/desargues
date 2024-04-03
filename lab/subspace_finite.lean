import Mathlib.LinearAlgebra.FiniteDimensional

open Submodule FiniteDimensional

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem pq_subspace_finite
(p q : V) :
Module.Finite K (span K {p, q}) := by
apply Module.Finite.span_of_finite
aesop -- proves Set.Finite {p,q}
