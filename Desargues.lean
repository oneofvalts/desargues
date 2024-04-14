import Mathlib.Tactic

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
  {PG : ProjectiveGeometry G} :
    G → G → Set G :=
  fun a b => if a = b then {a} else {c | PG.ell a b c}

theorem p_1
  {PG : ProjectiveGeometry G} :
    ∀ a, star (PG := PG) a a = {a} := by
  intro a
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

-- theorem p_3
--   {PG : ProjectiveGeometry G} :
--     ∀ a b c d p, a ∈ star (PG := PG) b p → p ∈ star (PG := PG) c d → a ≠ c →
--       star (PG := PG) a c ∩ star (PG := PG) b d ≠ ∅ := by
--   intro a b c d p
--   intro a_in_bp p_in_cd ac_neq inter_empty

end Desargues
