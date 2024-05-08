import Basic

open Set
open Basic

variable [DecidableEq G]

namespace Subspace

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

-- It is trivial that every subspace is a projective subgeometry.
instance
  [PG : ProjectiveGeometry G ell]
  [S : Subspace PG] :
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
  by_cases deq : (a = b ∨ a = c ∨ a = d ∨ a = p ∨ b = c ∨ b = d ∨ b = p
                ∨ c = d ∨ c = p ∨ d = p)
  · -- (ell : G → G → G → Prop)
    -- (a b c d p : G)
    -- (l1 : ∀ a b , ell a b a)
    -- (l2 : ∀ a b p q , ell a p q → ell b p q → p ≠ q → ell a b p)
    -- (abcdp_deq : a = b ∨ a = c ∨ a = d ∨ a = p ∨ b = c ∨ b = d ∨ b = p
    --              ∨ c = d ∨ c = p ∨ d = p)
    -- (pab_col : ell p a b)
    -- (pcd_col : ell p c d) :
    --   ∃ q, ell q a c ∧ ell q b d := by
    let ell' := fun a b c => S.E.restrict
                            (S.E.restrict
                            (S.E.restrict ell a) b) c
    apply l1_l2_eq_imp_l3 ell' a b c d p _ _ deq pab_col pcd_col
    · sorry
    · sorry
  · sorry
  -- match q_ex with
  -- | ⟨q, qac_col, qbd_col⟩ =>
  --   have q_in_ac :
  --       q ∈ star (ell := ell) a c := by
  --     unfold Basic.star
  --     simp
  --     split
  --     · sorry
  --     · sorry
  --   have ac_subseteq_E :
  --       star (ell := ell) a c ⊆ S.E := by
  --     apply S.closure a c a.property c.property
  --   apply ac_subseteq_E at q_in_ac
  --   use ⟨q, q_in_ac⟩
  done
  ⟩
  ⟩

end Subspace
