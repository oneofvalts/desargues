import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence

variable [DivisionRing K] [AddCommGroup V] [Module K V]

-- def index (X Y Z : Projectivization K V) : Fin 3 → Projectivization K V :=
-- fun i : Fin 3 => match i with
-- | 0 => X
-- | 1 => Y
-- | 2 => Z

class ProjectiveGeometry (point : Type u) where
ell : point → point → point → Prop
l1  : ∀ a b, ell a b a
l2  : ∀ a b p q, ell a p q → ell b p q → p ≠ q → ell a b p
l3  : ∀ a b c d p, ell p a b → ell p c d → ∃ q : point, ell q a c ∧ ell q b d

-- Every Projectivization is a ProjectiveGeometry
instance : ProjectiveGeometry (Projectivization K V) :=
⟨
-- fun X Y Z => ∃ k1 k2 k3 : K, ¬(k1 = 0 ∧ k2 = 0 ∧ k3 = 0) ∧ k1•X.rep + k2•Y.rep + k3•Z.rep = 0,
-- fun X Y Z => ¬ LinearIndependent K ![X.rep, Y.rep, Z.rep],
-- fun X Y Z => Projectivization.Dependent (index X Y Z),
fun X Y Z => ¬ Projectivization.Independent ![X, Y, Z],

sorry,
by
intro A B P Q
intro ABPcollinear BPQcollinear PneqQ
intro ABPnotcollinear
rw [<- Projectivization.independent_pair_iff_neq] at PneqQ
rw [Projectivization.independent_iff] at ABPcollinear 
rw [Projectivization.independent_iff] at BPQcollinear 
rw [Projectivization.independent_iff] at PneqQ 

done,
sorry
⟩
