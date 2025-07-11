import Basic

open Set
open Basic

namespace Structure

variable {G : Type*}
variable {ell : G → G → G → Prop}
variable [PG : ProjectiveGeometry G ell]

class ProjectiveSubgeometry
  (G' : Set G) where
  ell' : G' → G' → G' → Prop
  restriction : ∀ a b c : G', ell' a b c = ell a b c
  inst : ProjectiveGeometry G' ell'

theorem subspace_l1
  (E : Set G)
  (ell' : E → E → E → Prop)
  (restriction : ∀ a b c : E, ell' a b c = ell a b c)
  (a b : E) :
    ell' a b a := by
  rw [restriction a b a]
  apply PG.l1 a b

theorem subspace_l2
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
variable {E : Set G}

class Subspace
  (E : Set G) where
  closure : ∀ a b, a ∈ E → b ∈ E → star ell a b ⊆ E

variable [S : Subspace E]

-- It is trivial that every subspace is a projective subgeometry.
instance :
    ProjectiveSubgeometry (ell := ell) E where
  ell' := fun a b c => E.restrict (E.restrict (E.restrict ell a) b) c

  -- restriction is trivial.
  restriction := by
    intro a b c
    simp only [restrict_apply]

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
  · apply l1_l2_eq_imp_l3 a b c d p _ _ deq pab_col pcd_col
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
          q ∈ star ell a c := by
        simp only [star, mem_setOf_eq]
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
          star ell a c ⊆ E := by
        apply S.closure a c a.property c.property
      apply ac_subseteq_E at q_in_ac
      use ⟨q, q_in_ac⟩
  ⟩

-- By 2.2.5 (p_8) it follows that every line is a subspace.
-- In fact, I prove a general statement: Every star is a subspace. This means
-- singletons, too, are subspaces.
instance
  (a b : G) :
    Subspace (ell := ell) (star ell a b)  where
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
      simp only [star, ↓reduceIte, setOf_eq_eq_singleton, mem_singleton_iff] at z_in_xy
      exact mem_of_eq_of_mem z_in_xy y_in_ab

def galaxy
  (b c a : G) :
    Set G :=
  sUnion {star ell a x | x ∈ star ell b c}

-- Planes are subspaces will follow from 2.4.4, but it is a useful exercise to
-- prove it now, using the properties (P_i). As similar to above, I will prove
-- more generally that galaxies are subspaces.
instance
  (b c a: G) :
    Subspace (ell := ell) (galaxy (ell := ell) b c a)  where
  closure := by
    intro k l k_in_ab l_in_ab m m_in_xy
    obtain ⟨K, K_def, k_def⟩ := k_in_ab
    obtain ⟨L, L_def, l_def⟩ := l_in_ab
    obtain ⟨xₖ, ⟨xₖ_def, K_def⟩⟩ := K_def
    obtain ⟨xₗ, ⟨xₗ_def, L_def⟩⟩ := L_def
    rw [<- K_def] at k_def
    rw [<- L_def] at l_def
    unfold galaxy
    rw [mem_sUnion]
    -- We split the proof into two cases where one is the degenerate
    -- configuration and the other is not. If a, b, c are collinear, then we
    -- actually do not have a real galaxy. We either have a line, or a single
    -- point. This case is already solved above, we will get an appropriate
    -- instance and then use the closure.
    by_cases abc_col : ell a b c
    · have bc_subspace : Subspace (ell := ell) (star ell b c) := inferInstance
      let closure := bc_subspace.closure
      sorry
    -- In the real case, we will use abc_inter_sing or a variant.
    · rename ¬ ell a b c => abc_ncol
      sorry

end Structure
