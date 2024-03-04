-- This module serves as the root of the `Desargues` library.
-- Import modules here that should be built as part of the library.
import «Desargues».Basic
import Mathlib.LinearAlgebra.Projectivization.Basic

variable [DivisionRing K] [AddCommGroup V] [Module K V]

class ProjectiveGeometry (point : Type u) where
ell : point → point → point → Prop
l1  : ∀ a b, ell a b a
l2  : ∀ a b p q, ell a p q → ell b p q → p ≠ q → ell a b p
l3  : ∀ a b c d p, ell p a b → ell p c d → ∃ q : point, ell q a c ∧ ell q b d

-- Every Projectivization is a ProjectiveGeometry
instance : ProjectiveGeometry (Projectivization K V) :=
⟨
fun X Y Z => ∃ k1 k2 k3 : K, ¬(k1 = 0 ∧ k2 = 0 ∧ k3 = 0)
∧ k1•X.rep + k2•Y.rep + k3•Z.rep = 0,

by
intro A B
use 1, 0, -1
constructor
intro eq
aesop
simp,

by
intros A B P Q
intro APQreside BPQreside PnotQ
rcases APQreside with ⟨ka, kp, kq, apqknotzero, apqcomb⟩
rcases BPQreside with ⟨kb, kkp, kkq, bpqknotzero, bpqcomb⟩
obtain rfl | kqnotzero := eq_or_ne kq 0
done
,

sorry
⟩
