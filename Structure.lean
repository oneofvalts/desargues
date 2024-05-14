import Basic

open Set
open Basic

variable [DecidableEq G]

namespace Structure

class Subspace
  (PG : ProjectiveGeometry G ell) where
  E : Set G
  closure : ∀ a b, a ∈ E → b ∈ E → star (ell := ell) a b ⊆ E

class ProjectiveSubgeometry
  (PG : ProjectiveGeometry G ell)
  (G' : Set G) where
  ell' : G' → G' → G' → Prop
  restriction : ∀ a b c : G', ell' a b c = ell a b c
  inst : ProjectiveGeometry G' ell'

theorem subspace_l1
  [PG : ProjectiveGeometry G ell]
  [S : Subspace PG]
  (ell' : S.E → S.E → S.E → Prop)
  (restriction : ∀ a b c : S.E, ell' a b c = ell a b c)
  (a b : S.E) :
    ell' a b a := by
  rw [restriction a b a]
  apply PG.l1 a b

theorem subspace_l2
  [PG : ProjectiveGeometry G ell]
  [S : Subspace PG]
  (ell' : S.E → S.E → S.E → Prop)
  (restriction : ∀ a b c : S.E, ell' a b c = ell a b c)
  (a b p q : S.E)
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
  [S : Subspace PG] :
    ProjectiveSubgeometry PG S.E where
  ell' := fun a b c => S.E.restrict (S.E.restrict (S.E.restrict ell a) b) c

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
  let ell' := fun a b c => S.E.restrict
                          (S.E.restrict
                          (S.E.restrict ell a) b) c
  simp only [restrict]
  intro a b c d p pab_col pcd_col
  have q_ex :
      ∃ q, ell q a c ∧ ell q b d := by
    { apply PG.l3 a b c d p pab_col pcd_col }
  by_cases deq : (a = b ∨ a = c ∨ a = d ∨ a = p ∨ b = c ∨ b = d ∨ b = p
                ∨ c = d ∨ c = p ∨ d = p)
  · apply l1_l2_eq_imp_l3 ell' a b c d p _ _ deq pab_col pcd_col
    · intro a b
      apply subspace_l1 ell' _ a b
      exact fun a b c ↦ rfl
    · intro a b p q apq_col bpq_col pq_neq
      apply subspace_l2 ell' _ a b p q apq_col bpq_col pq_neq
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
          star (ell := ell) a c ⊆ S.E := by
        apply S.closure a c a.property c.property
      apply ac_subseteq_E at q_in_ac
      use ⟨q, q_in_ac⟩
    done
  ⟩

abbrev Line
  (ell : G → G → G → Prop)
  (a b : G) :
    Set G :=
  {c : G | a ≠ b ∧ ell a b c}

-- By 2.2.5 (p_8 and p_9) it follows that every line is a subspace.

abbrev Plane
  [ProjectiveGeometry G ell]
  (a b c : G)
  (δ := Line (ell := ell) b c) :
    Set G :=
  sUnion {Basic.star (ell := ell) a x | x ∈ δ}

end Structure
