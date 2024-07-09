import Basic

open Set
open Basic

variable [DecidableEq G]

namespace Structure

class Subspace
  (PG : ProjectiveGeometry G ell)
  (E : Set G) where
  closure : ∀ a b, a ∈ E → b ∈ E → star (ell := ell) a b ⊆ E

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

-- It is trivial that every subspace is a projective subgeometry.
instance
  [PG : ProjectiveGeometry G ell]
  (E : Set G)
  [S : Subspace PG E] :
    ProjectiveSubgeometry PG E where
  ell' := fun a b c => E.restrict (E.restrict (E.restrict ell a) b) c

  -- restriction is trivial.
  restriction := by
    intro a b c
    simp
    done

  inst := ⟨
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
        case inl aacc_eq =>
          have ac_eq : a = c := by { exact SetCoe.ext aacc_eq }
          match deq with
          | ⟨_, ac_neq, _⟩ => contradiction
        case inr aacc_neq =>
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
    done
  ⟩

class Line
  [ProjectiveGeometry G ell]
  (a b : G) where
  δ : Set G
  str : δ = star (ell := ell) a b
  ab_neq : a ≠ b

-- By 2.2.5 (p_8) it follows that every line is a subspace.
-- See that Line.ab_neq is never used.
instance
  [PG : ProjectiveGeometry G ell]
  [L : Line (ell := ell) a b] :
    Subspace PG L.δ where
  closure := by
    intro x y x_in_ab y_in_ab
    intro z z_in_xy
    by_cases xy_neq : x = y
    case neg =>
      rw [Line.str] at x_in_ab
      rw [Line.str] at y_in_ab
      have xy_ab_eq : _ :=
        by apply p_8 (ell := ell) x y a b x_in_ab y_in_ab xy_neq
      rw [Line.str]
      rw [<- xy_ab_eq]
      exact z_in_xy
    case pos =>
      rw [xy_neq] at z_in_xy
      simp at z_in_xy
      rw [<- xy_neq] at z_in_xy
      rw [z_in_xy]
      exact x_in_ab

class Plane
  [ProjectiveGeometry G ell]
  (b c a : G)
  (L : Line (ell := ell) b c) where
  π : Set G
  str : π = sUnion {star (ell := ell) a x | x ∈ L.δ}
  a_nin_line : a ∉ L.δ

end Structure
