import Mathlib.Tactic

open Set

variable [DecidableEq G]

namespace Subspace

class ProjectiveGeometry
  (G : Type u)
  (ell : G → G → G → Prop) where
  l1  : ∀ a b , ell a b a
  l2  : ∀ a b p q , ell a p q → ell b p q → p ≠ q → ell a b p
  l3  : ∀ a b c d p, ell p a b → ell p c d → ∃ q, ell q a c ∧ ell q b d

def star
  (ell : G → G → G → Prop)
  (a b : G) :
    Set G :=
  {c | if a = b then c = a else ell a b c}

class Subspace
  (PG : ProjectiveGeometry G ell) where
  E : Set G
  closure : ∀ a b, a ∈ E → b ∈ E → star ell a b ⊆ E

class ProjectiveSubgeometry
  (PG : ProjectiveGeometry G ell)
  (G' : Set G) where
  ell' : G' → G' → G' → Prop
  restriction : ∀ a b c : G', ell' a b c = ell a b c
  inst : ProjectiveGeometry G' ell'

-- It is trivial that every subspace is a projective subgeometry.
instance
  (PG : ProjectiveGeometry G ell)
  (S : Subspace PG) :
    ProjectiveSubgeometry PG S.E :=
  ⟨
  fun a b c => S.E.restrict (S.E.restrict (S.E.restrict ell a) b) c,

  -- restriction is trivial.
  by
  intro a b c
  simp
  done,

  ⟨
  by
  simp only [restrict]
  intro a b
  apply PG.l1 a b
  done,

  by
  simp only [restrict]
  intro a b p q apq_col bpq_col pq_neq
  apply PG.l2 a b p q apq_col bpq_col
  intro ppqq_eq
  have pq_eq : p = q := by { exact SetCoe.ext ppqq_eq }
  contradiction
  done,

  by
  simp only [restrict]
  intro a b c d p pab_col pcd_col
  have q_ex :
      ∃ q, ell q a c ∧ ell q b d := by
    { apply PG.l3 a b c d p pab_col pcd_col }
  match q_ex with
  | ⟨q, qac_col, qbd_col⟩ =>
    have q_in_E :
        q ∈ star ell a c := by
      unfold star
      simp
      split
      case inl ac_eq =>
        rw [ac_eq] at qac_col
        -- TODO: I don't have the symmetry theorems here.
        sorry
      case inr ac_neq =>
        -- Again, this will be proved with symmetry theorems.
        sorry
    have ac_subseteq_E :
        star ell a c ⊆ S.E := by
      apply S.closure a c a.property c.property
    apply ac_subseteq_E at q_in_E
    use ⟨q, q_in_E⟩
  done
  ⟩
  ⟩

end Subspace
