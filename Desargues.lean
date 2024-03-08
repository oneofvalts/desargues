import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence

variable [DivisionRing K] [AddCommGroup V] [Module K V]

-- def index (X Y Z : Projectivization K V) : Fin 3 → Projectivization K V :=
-- fun i : Fin 3 => match i with
-- | 0 => X
-- | 1 => Y
-- | 2 => Z

def coeff (k1 k2 k3 : K) : Fin 3 → K :=
fun i : Fin 3 => match i with
| 0 => k1
| 1 => k2
| 2 => k3

class ProjectiveGeometry (point : Type u) where
ell : point → point → point → Prop
l1  : ∀ a b, ell a b a
l2  : ∀ a b p q, ell a p q → ell b p q → p ≠ q → ell a b p
l3  : ∀ a b c d p, ell p a b → ell p c d → ∃ q : point, ell q a c ∧ ell q b d

theorem rep_comp_3 (X Y Z : Projectivization K V) :
Projectivization.rep ∘ ![X, Y, Z] = ![X.rep, Y.rep, Z.rep] := by
exact List.ofFn_inj.mp rfl

theorem rep_comp_2 (X Y : Projectivization K V) :
Projectivization.rep ∘ ![X, Y] = ![X.rep, Y.rep] := by
exact List.ofFn_inj.mp rfl

theorem l2_rep (a b p q : V) : ¬ LinearIndependent K ![a, p, q] ->
¬ LinearIndependent K ![b, p, q] -> LinearIndependent K ![p, q] ->
¬ LinearIndependent K ![a, b, p] := by
sorry

-- Every Projectivization is a ProjectiveGeometry
instance : ProjectiveGeometry (Projectivization K V) :=
⟨
-- fun X Y Z => ∃ k1 k2 k3 : K, ¬(k1 = 0 ∧ k2 = 0 ∧ k3 = 0) ∧ k1•X.rep + k2•Y.rep + k3•Z.rep = 0,
-- fun X Y Z => ¬ LinearIndependent K ![X.rep, Y.rep, Z.rep],
-- fun X Y Z => Projectivization.Dependent (index X Y Z),
fun X Y Z => ¬ Projectivization.Independent ![X, Y, Z],

by
intro A B
rw [Projectivization.independent_iff, rep_comp_3]
rw [not_linearIndependent_iff]
use {0, 1, 2}, ![1, 0, -1]
constructor
{ sorry }
{ simp }
-- rw [Projectivization.independent_iff, rep_comp_3] at ABAcollinear
-- #print LinearIndependent.repr ABAcollinear (Submodule.span K (Set.range ![A.rep, B.rep, A.rep]))
done,

by
intro A B P Q
intro ABPcollinear BPQcollinear PneqQ
rw [<- Projectivization.independent_pair_iff_neq] at PneqQ
rw [Projectivization.independent_iff, rep_comp_3] at ABPcollinear
rw [Projectivization.independent_iff, rep_comp_3] at BPQcollinear
rw [Projectivization.independent_iff, rep_comp_2] at PneqQ
rw [Projectivization.independent_iff, rep_comp_3]
apply l2_rep A.rep B.rep P.rep Q.rep
exact ABPcollinear
exact BPQcollinear
exact PneqQ
done,

sorry
⟩
