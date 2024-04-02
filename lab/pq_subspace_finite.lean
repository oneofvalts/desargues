import Mathlib.RingTheory.Finiteness

open Submodule

variable [DivisionRing K] [AddCommGroup V] [Module K V] [DecidableEq V]

theorem pq_subspace_finite (p q : V) : Module.Finite K (span K {p, q}) := by
apply Module.Finite.span_of_finite
aesop -- proves Set.Finite {p,q}
