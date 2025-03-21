import Basic
import LeanCopilot

open Set
open Basic

namespace Structure

class ProjectiveSubgeometry
  (PG : ProjectiveGeometry G ell)
  (G' : Set G) where
  ell' : G' → G' → G' → Prop
  restriction : ∀ a b c : G', ell' a b c = ell a b c
  inst : ProjectiveGeometry G' ell'

theorem subspace_l1
  [PG : ProjectiveGeometry G ell]
  (E : Set G)
  (ell' : E → E → E → Prop)
  (restriction : ∀ a b c : E, ell' a b c = ell a b c)
  (a b : E) :
    ell' a b a := by
  rw [restriction a b a]
  apply PG.l1 a b

theorem subspace_l2
  [PG : ProjectiveGeometry G ell]
  (E : Set G)
  (ell' : E → E → E → Prop)
  (restriction : ∀ a b c : E, ell' a b c = ell a b c)
  (a b p q : E)
  (apq_col : ell' a p q)
  (bpq_col : ell' b p q)
  (pq_neq : p ≠ q) :
    ell' a b p := by
  rw [restriction]
  rw [restriction] at apq_col
  rw [restriction] at bpq_col
  apply PG.l2 a b p q apq_col bpq_col
  intro ppqq_eq
  have pq_eq : p = q := by { exact SetCoe.ext ppqq_eq }
  contradiction

variable [DecidableEq G]

class Subspace
  (PG : ProjectiveGeometry G ell)
  (E : Set G) where
  closure : ∀ a b, a ∈ E → b ∈ E → star (ell := ell) a b ⊆ E

-- It is trivial that every subspace is a projective subgeometry.
instance
  [PG : ProjectiveGeometry G ell]
  [S : Subspace PG E] :
    ProjectiveSubgeometry PG E where
  ell' := fun a b c => E.restrict (E.restrict (E.restrict ell a) b) c

  -- restriction is trivial.
  restriction := by
    intro a b c
    simp

  inst := ⟨
  by
  simp only [restrict]
  intro a b
  apply PG.l1 a b,

  by
  simp only [restrict]
  intro a b p q apq_col bpq_col pq_neq
  apply PG.l2 a b p q apq_col bpq_col
  intro ppqq_eq
  have pq_eq : p = q := by { exact SetCoe.ext ppqq_eq }
  contradiction,

  by
  let ell' := fun a b c => E.restrict
                          (E.restrict
                          (E.restrict ell a) b) c
  simp only [restrict]
  intro a b c d p pab_col pcd_col
  have q_ex :
      ∃ q, ell q a c ∧ ell q b d := by
    { apply PG.l3 a b c d p pab_col pcd_col }
  by_cases deq : (a = b ∨ a = c ∨ a = d ∨ a = p ∨ b = c ∨ b = d ∨ b = p
                ∨ c = d ∨ c = p ∨ d = p)
  · apply l1_l2_eq_imp_l3 ell' a b c d p _ _ deq pab_col pcd_col
    · intro a b
      apply subspace_l1 (ell := ell) E ell' _ a b
      exact fun a b c ↦ rfl
    · intro a b p q apq_col bpq_col pq_neq
      apply subspace_l2 (ell := ell) E ell' _ a b p q apq_col bpq_col pq_neq
      exact fun a b c ↦ rfl
  · push_neg at deq
    match q_ex with
    | ⟨q, qac_col, qbd_col⟩ =>
      have q_in_ac :
          q ∈ star (ell := ell) a c := by
        simp
        split
        case isTrue aacc_eq =>
          have ac_eq : a = c := by { exact SetCoe.ext aacc_eq }
          match deq with
          | ⟨_, ac_neq, _⟩ => contradiction
        case isFalse aacc_neq =>
          apply rel_sym_bca q a c
          · intro a b
            apply PG.l1 a b
          · intro a b p q apq_col bpq_col pq_neq
            apply PG.l2 a b p q apq_col bpq_col pq_neq
          · exact qac_col
      have ac_subseteq_E :
          star (ell := ell) a c ⊆ E := by
        apply S.closure a c a.property c.property
      apply ac_subseteq_E at q_in_ac
      use ⟨q, q_in_ac⟩
  ⟩

-- By 2.2.5 (p_8) it follows that every line is a subspace.
-- In fact, I prove a general statement: Every star is a subspace. This means
-- singletons, too, are subspaces.
instance
  [PG : ProjectiveGeometry G ell]
  (a b : G) :
    Subspace PG (star (ell := ell) a b)  where
  closure := by
    intro x y x_in_ab y_in_ab z z_in_xy
    by_cases xy_neq : x = y
    case neg =>
      have xy_ab_eq :=
        by apply p_8 (ell := ell) x y a b x_in_ab y_in_ab xy_neq
      rw [<- xy_ab_eq]
      exact z_in_xy
    case pos =>
      rw [xy_neq] at z_in_xy
      simp at z_in_xy
      rw [<- xy_neq] at z_in_xy
      rw [z_in_xy]
      exact x_in_ab

def galaxy
  [ProjectiveGeometry G ell]
  (b c a : G) :
    Set G :=
  sUnion {star (ell := ell) a x | x ∈ star (ell := ell) b c}

-- Planes are subspaces will follow from 2.4.4, but it is a useful exercise to
-- prove it now, using the properties (P_i). As similar to above, I will prove
-- more generally that galaxies are subspaces.
instance
  [PG : ProjectiveGeometry G ell]
  (b c a: G) :
    Subspace PG (galaxy (ell := ell) b c a)  where
  closure := by
    intro k l k_in_ab l_in_ab m m_in_xy
    unfold galaxy at k_in_ab
    unfold galaxy at l_in_ab
    unfold galaxy
    simp

end Structure
