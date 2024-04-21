import Mathlib.Tactic

open Set

namespace Desargues

variable [DecidableEq G]

-- A projective geometry is a set G together with a ternary relation
-- ℓ ⊆ G × G × G satisfying L₁, L₂ and L₃. (p. 26)
class ProjectiveGeometry
  (G : Type u) where
  ell : G → G → G → Prop
  l1  : ∀ a b, ell a b a
  l2  : ∀ a b p q, ell a p q → ell b p q → p ≠ q → ell a b p
  l3  : ∀ a b c d p, ell p a b → ell p c d → ∃ q : G, ell q a c ∧ ell q b d

variable (PG : ProjectiveGeometry G)

-- Any ternary relation ℓ which satisfies L₁ and L₂ is symmetric. From
-- "ℓ(a, b, c)", ell feeded with any permutations of "abc" can be proved.
-- First, "acb" and "cab" will be derived. These cycles will generate the
-- group of permutations of three objects. (p. 27)
theorem rel_sym_acb
  {G : Type u}
  {PG : ProjectiveGeometry G}
  (a b c : G)
  (abc_col : PG.ell a b c) :
    PG.ell a c b := by
  obtain rfl | bc_neq := eq_or_ne b c
  · exact abc_col -- b = c, meaning abc and acb becomes abb
  · apply PG.l2 a c b c
    · exact abc_col
    · apply PG.l1 c b
    · exact bc_neq

theorem rel_sym_cab
  {G : Type u}
  {PG : ProjectiveGeometry G}
  (a b c : G)
  (abc_col : PG.ell a b c) :
    PG.ell c a b := by
  obtain rfl | bc_neq := eq_or_ne b c
  · apply PG.l1 b a
  · apply PG.l2 c a b c
    · apply PG.l1 c b
    · exact abc_col
    · exact bc_neq

-- Now we can easily generate the other three.
theorem rel_sym_bca
  {G : Type u}
  {PG : ProjectiveGeometry G}
  (a b c : G)
  (abc_col : PG.ell a b c) :
    PG.ell b c a := by
  apply rel_sym_cab c a b
  apply rel_sym_cab a b c
  exact abc_col

theorem rel_sym_bac
  {G : Type u}
  {PG : ProjectiveGeometry G}
  (a b c : G)
  (abc_col : PG.ell a b c) :
    PG.ell b a c := by
  apply rel_sym_cab a c b
  apply rel_sym_acb a b c
  exact abc_col

theorem rel_sym_cba
  {G : Type u}
  {PG : ProjectiveGeometry G}
  (a b c : G)
  (abc_col : PG.ell a b c) :
    PG.ell c b a := by
  apply rel_sym_cab b a c
  apply rel_sym_bac a b c
  exact abc_col

-- An isomorphism of projective geometries is a bijective map g : G₁ → G₂
-- satisfying ℓ₁(a, b, c) iff ℓ₂(ga, gb, gc). When G₁ = G₂ one says that
-- g is a collineation. (p. 27)
class PG_Iso
  {G₁ : Type u_1}
  {G₂ : Type u_2}
  {PG₁ : ProjectiveGeometry G₁}
  {PG₂ : ProjectiveGeometry G₂}
  (f : G₁ → G₂) where
  bij      : Function.Bijective f
  pres_col : ∀ (a b c : G₁), PG₁.ell a b c ↔ PG₂.ell (f a) (f b) (f c)

-- Let G = (G, ℓ) be a projective geometry. Then the operator ⋆ : G × G →
-- Powerset(G) defined by a ⋆ b := {c ∈ G / ℓ(a, b, c)} if a ≠ b and a ⋆
-- a := {a} satisfies P₁, P₂ and P₃.
def star
  {PG : ProjectiveGeometry G}
  (a b : G) :
    Set G :=
  {c : G | if a = b then c = a else PG.ell a b c}

theorem p_1
  {PG : ProjectiveGeometry G}
  (a : G) :
    star (PG := PG) a a = {a} := by
  unfold star
  simp

theorem p_2
  {PG : ProjectiveGeometry G} :
    ∀ a b, a ∈ star (PG := PG) b a := by
  intro a b
  unfold star
  obtain rfl | _ := eq_or_ne a b
  · simp
  · split
    case inr.inl eq =>
      rw [eq]
      simp
    case inr.inr _ =>
      simp
      apply rel_sym_bca a b a
      apply PG.l1 a b

lemma star_imp_ell
  {PG : ProjectiveGeometry G}
  (x y z : G)
  (x_in_yz : x ∈ star (PG := PG) y z) :
    PG.ell x y z := by
  obtain rfl | yz_neq := eq_or_ne y z
  · apply rel_sym_bca y x y
    apply PG.l1 y x
  · unfold star at x_in_yz
    split at x_in_yz
    case inr.inl eq => apply yz_neq at eq; contradiction
    case inr.inr _ =>
      simp at x_in_yz
      apply rel_sym_cab y z x
      exact x_in_yz

lemma abc_ncol_imp_neq
  {PG : ProjectiveGeometry G}
  (a b c : G)
  (abc_ncol : ¬ PG.ell a b c):
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  constructor
  case left =>
    intro ab_eq
    rw [ab_eq] at abc_ncol
    apply abc_ncol
    apply rel_sym_cab b c b
    apply PG.l1 b c
  case right =>
    constructor
    case left =>
      intro ac_eq
      rw [ac_eq] at abc_ncol
      apply abc_ncol
      apply PG.l1 c b
    case right =>
      intro bc_eq
      rw [bc_eq] at abc_ncol
      apply abc_ncol
      apply rel_sym_bca c a c
      apply PG.l1 c a

theorem p_3
  {PG : ProjectiveGeometry G}
  (a b c d p : G)
  (a_in_bp : a ∈ star (PG := PG) b p)
  (p_in_cd : p ∈ star (PG := PG) c d)
  (ac_neq : a ≠ c) :
    star (PG := PG) a c ∩ star (PG := PG) b d ≠ ∅ := by
  intro inter_empty
  by_cases abc_col : PG.ell a b c
  · have b_in_inter :
        b ∈ star (PG := PG) a c ∩ star (PG := PG) b d := by
      rw [inter_def]
      simp
      constructor
      · unfold star
        split
        case left.inl eq =>
          apply ac_neq at eq
          contradiction
        case left.inr neq =>
          simp
          apply rel_sym_acb a b c
          exact abc_col
      · unfold star
        split
        case right.inl _ =>
          simp
        case right.inr _ =>
          simp
          apply PG.l1 b d
    rw [inter_empty] at b_in_inter
    exact b_in_inter
  · have abp_col :
        PG.ell a b p := by
      apply star_imp_ell a b p a_in_bp
    have pcd_col :
        PG.ell p c d := by
      apply star_imp_ell p c d p_in_cd
    have abc_neq :
        a ≠ b ∧ a ≠ c ∧ b ≠ c := by
      apply abc_ncol_imp_neq a b c
      exact abc_col
    have ab_neq :
        a ≠ b := by
      cases abc_neq with
      | intro left _ => exact left
    have bp_neq :
        b ≠ p := by
      intro bp_eq
      rw [bp_eq] at a_in_bp
      have ab_eq :
          a = b := by
        unfold star at a_in_bp
        simp at a_in_bp
        rw [<- bp_eq] at a_in_bp
        exact a_in_bp
      contradiction
    have bd_neq :
        b ≠ d := by
      intro bd_eq
      rw [<- bd_eq] at pcd_col
      apply abc_col -- ℓ(a, c, b) follows from L₂, now.
      apply rel_sym_acb a c b
      apply PG.l2 a c b p
      · exact abp_col
      · apply rel_sym_bca p c b
        exact pcd_col
      · exact bp_neq
    have q_ex :
        exists q, PG.ell q a c ∧ PG.ell q b d := by
      apply PG.l3 a b c d p
      · apply rel_sym_cab a b p
        exact abp_col
      · exact pcd_col
    match q_ex with
    | ⟨q, qac_col, qbd_col⟩ =>
      have q_in_inter :
          q ∈ star (PG := PG) a c ∩ star (PG := PG) b d := by
        rw [inter_def]
        simp
        constructor
        · unfold star
          split
          case left.inl ac_eq =>
            contradiction
          case left.inr _ =>
            simp
            apply rel_sym_bca q a c
            exact qac_col
        · unfold star
          split
          case right.inl bd_eq =>
            contradiction
          case right.inr _ =>
            simp
            apply rel_sym_bca q b d
            exact qbd_col
      rw [inter_empty] at q_in_inter
      exact q_in_inter

infix:50 " ⋆ " => star

theorem p_4
  {PG : ProjectiveGeometry G}
  (a b c : G)
  (a_in_bc : a ∈ star (PG := PG) b c)
  (ab_neq : a ≠ b) :
    c ∈ star (PG := PG) a b := by
  have a_in_ca :
      a ∈ star (PG := PG) c a := by
    apply p_2 a c
  -- a c b c a
  have inter_nempty :
      star (PG := PG) a b ∩ star (PG := PG) c c ≠ ∅ := by
    apply p_3 a c b c a
    · exact a_in_ca
    · exact a_in_bc
    · exact ab_neq
  unfold star at inter_nempty
  simp at inter_nempty
  apply inter_nempty

theorem p_5
  {PG : ProjectiveGeometry G}
  (a b c : G)
  (a_in_bc : a ∈ star (PG := PG) b c) :
    star (PG := PG) a b ⊆ star (PG := PG) b c := by

end Desargues
