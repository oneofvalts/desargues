-- import Mathlib.Tactic
import Mathlib.Data.Set.Card
-- import Mathlib
-- import LeanCopilot

open Set

namespace Basic

-- A projective geometry is a set G together with a ternary relation
-- ℓ ⊆ G × G × G satisfying L₁, L₂ and L₃. (p. 26)
class ProjectiveGeometry
  (G : Type u)
  (ell : G → G → G → Prop) where
  l1  : ∀ a b , ell a b a
  l2  : ∀ a b p q , ell a p q → ell b p q → p ≠ q → ell a b p
  l3  : ∀ a b c d p, ell p a b → ell p c d → ∃ q, ell q a c ∧ ell q b d

-- Any ternary relation ℓ which satisfies L₁ and L₂ is symmetric. From
-- "ℓ(a, b, c)", ell feeded with any permutations of "abc" can be proved.
-- First, "acb" and "cab" will be derived. These cycles will generate the
-- group of permutations of three objects. (p. 27)
theorem rel_sym_acb
  {ell : G → G → G → Prop}
  (a b c : G)
  (l1 : ∀ a b , ell a b a)
  (l2 : ∀ a b p q , ell a p q → ell b p q → p ≠ q → ell a b p)
  (abc_col : ell a b c) :
    ell a c b := by
  obtain rfl | bc_neq := eq_or_ne b c
  -- tauto
  · -- b = c, meaning abc and acb becomes abb
    exact abc_col
  · apply l2 a c b c
    · exact abc_col
    · apply l1 c b
    · exact bc_neq

theorem rel_sym_cab
  {ell : G → G → G → Prop}
  (a b c : G)
  (l1 : ∀ a b , ell a b a)
  (l2 : ∀ a b p q , ell a p q → ell b p q → p ≠ q → ell a b p)
  (abc_col : ell a b c) :
    ell c a b := by
  obtain rfl | bc_neq := eq_or_ne b c
  -- tauto
  -- tauto
  · apply l1 b a
  · apply l2 c a b c
    · apply l1 c b
    · exact abc_col
    · exact bc_neq

-- Now we can easily generate the other three.
theorem rel_sym_bca
  {ell : G → G → G → Prop}
  (a b c : G)
  (l1 : ∀ a b , ell a b a)
  (l2 : ∀ a b p q , ell a p q → ell b p q → p ≠ q → ell a b p)
  (abc_col : ell a b c) :
    ell b c a := by
  apply rel_sym_cab c a b l1 l2
  apply rel_sym_cab a b c l1 l2
  exact abc_col

theorem rel_sym_bac
  {ell : G → G → G → Prop}
  (a b c : G)
  (l1 : ∀ a b , ell a b a)
  (l2 : ∀ a b p q , ell a p q → ell b p q → p ≠ q → ell a b p)
  (abc_col : ell a b c) :
    ell b a c := by
  apply rel_sym_cab a c b l1 l2
  apply rel_sym_acb a b c l1 l2
  exact abc_col

theorem rel_sym_cba
  {ell : G → G → G → Prop}
  (a b c : G)
  (l1 : ∀ a b , ell a b a)
  (l2 : ∀ a b p q , ell a p q → ell b p q → p ≠ q → ell a b p)
  (abc_col : ell a b c) :
    ell c b a := by
  apply rel_sym_cab b a c l1 l2
  apply rel_sym_bac a b c l1 l2
  exact abc_col

theorem ncol_imp_neq
  [PG : ProjectiveGeometry G ell]
  (a b c : G)
  (abc_ncol : ¬ ell a b c):
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  constructor
  case left =>
    intro ab_eq
    rw [ab_eq] at abc_ncol
    apply abc_ncol
    apply rel_sym_cab b c b PG.l1 PG.l2 (PG.l1 b c)
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
      apply rel_sym_bca c a c PG.l1 PG.l2 (PG.l1 c a)

theorem l1_l2_eq_imp_l3
  (ell : G → G → G → Prop)
  (a b c d p : G)
  (l1 : ∀ a b , ell a b a)
  (l2 : ∀ a b p q , ell a p q → ell b p q → p ≠ q → ell a b p)
  (abcdp_deq : a = b ∨ a = c ∨ a = d ∨ a = p ∨ b = c ∨ b = d ∨ b = p
               ∨ c = d ∨ c = p ∨ d = p)
  (pab_col : ell p a b)
  (pcd_col : ell p c d) :
    ∃ q, ell q a c ∧ ell q b d := by
  rcases abcdp_deq
  case inl ab_eq =>
    rw [ab_eq]
    use b
    constructor
    case h.left =>
      apply rel_sym_cab b c b l1 l2 (l1 b c)
    case h.right =>
      apply rel_sym_cab b d b l1 l2 (l1 b d)
  case inr rest =>
    rcases rest
    case inl ac_eq =>
      rw [ac_eq]
      use b
      constructor
      case h.left =>
        apply rel_sym_bca c b c l1 l2 (l1 c b)
      case h.right =>
        apply rel_sym_cab b d b l1 l2 (l1 b d)
    case inr rest =>
      rcases rest
      case inl ad_eq =>
        rw [ad_eq]
        use d
        constructor
        case h.left =>
          apply rel_sym_cab d c d l1 l2 (l1 d c)
        case h.right =>
          apply l1 d b
      case inr rest =>
        rcases rest
        case inl ap_eq =>
          rw [ap_eq]
          use d
          constructor
          case h.left =>
            apply rel_sym_cab p c d l1 l2 pcd_col
          case h.right =>
            apply l1 d b
        case inr rest =>
          rcases rest
          case inl bc_eq =>
            rw [bc_eq]
            use c
            constructor
            case h.left =>
              apply l1 c a
            case h.right =>
              apply rel_sym_cab c d c l1 l2 (l1 c d)
          case inr rest =>
          rcases rest
          case inl bd_eq =>
            rw [bd_eq]
            use c
            constructor
            case h.left =>
              apply l1 c a
            case h.right =>
              apply rel_sym_bca d c d l1 l2 (l1 d c)
          case inr rest =>
            rcases rest
            case inl bp_eq =>
              rw [bp_eq]
              use c
              constructor
              case h.left =>
                apply l1 c a
              case h.right =>
                apply rel_sym_bac p c d l1 l2 pcd_col
            case inr rest =>
              rcases rest
              case inl cd_eq =>
                rw [cd_eq]
                use d
                constructor
                case h.left =>
                  apply l1 d a
                case h.right =>
                  apply l1 d b
              case inr rest =>
                rcases rest
                case inl cp_eq =>
                  rw [cp_eq]
                  use b
                  constructor
                  case h.left =>
                    apply rel_sym_cba p a b l1 l2 pab_col
                  case h.right =>
                    apply rel_sym_cab b d b l1 l2 (l1 b d)
                case inr dp_eq =>
                  rw [dp_eq]
                  use a
                  constructor
                  case h.left =>
                    apply rel_sym_cab a c a l1 l2 (l1 a c)
                  case h.right =>
                    apply rel_sym_bca p a b l1 l2 pab_col

-- An isomorphism of projective geometries is a bijective map g : G₁ → G₂
-- satisfying ℓ₁(a, b, c) iff ℓ₂(ga, gb, gc). When G₁ = G₂ one says that
-- g is a collineation. (p. 27)
class PG_Iso
  [ProjectiveGeometry G₁ ell₁]
  [ProjectiveGeometry G₂ ell₂]
  (f : G₁ → G₂) where
  bij      : Function.Bijective f
  pres_col : ∀ (a b c : G₁), ell₁ a b c ↔ ell₂ (f a) (f b) (f c)

variable [DecidableEq G]

-- Let G = (G, ℓ) be a projective geometry. Then the operator ⋆ : G × G →
-- Powerset(G) defined by a ⋆ b := {c ∈ G / ℓ(a, b, c)} if a ≠ b and a ⋆
-- a := {a} satisfies P₁, P₂ and P₃.
@[simp]
def star
  (ell : G → G → G → Prop)
  (a b : G) :
    Set G :=
  {c : G | if a = b then c = a else ell a b c}

theorem p_1
  [ProjectiveGeometry G ell]
  (a : G) :
    star ell a a = {a} := by
  unfold star
  simp

theorem p_2
  [PG : ProjectiveGeometry G ell] :
    ∀ a b, a ∈ star ell b a := by
  intro a b
  unfold star
  obtain rfl | _ := eq_or_ne a b
  · simp
  · split
    case inr.isTrue eq =>
      rw [eq]
      simp
    case inr.isFalse _ =>
      simp
      apply rel_sym_bca a b a PG.l1 PG.l2 (PG.l1 a b)

theorem star_imp_ell
  [PG : ProjectiveGeometry G ell]
  (x y z : G)
  (x_in_yz : x ∈ star ell y z) :
    ell x y z := by
  obtain rfl | yz_neq := eq_or_ne y z
  · apply rel_sym_bca y x y PG.l1 PG.l2 (PG.l1 y x)
  · unfold star at x_in_yz
    split at x_in_yz
    case inr.isTrue eq => apply yz_neq at eq; contradiction
    case inr.isFalse _ =>
      simp at x_in_yz
      apply rel_sym_cab y z x PG.l1 PG.l2 x_in_yz

theorem p_3
  [PG : ProjectiveGeometry G ell]
  (a b c d p : G)
  (a_in_bp : a ∈ star ell b p)
  (p_in_cd : p ∈ star ell c d)
  (ac_neq : a ≠ c) :
    star ell a c ∩ star ell b d ≠ ∅ := by
  intro inter_empty
  by_cases abc_col : ell a b c
  · have b_in_inter :
        b ∈ star ell a c ∩ star ell b d := by
      rw [inter_def]
      simp
      constructor
      · split
        case left.isTrue eq =>
          apply ac_neq at eq
          contradiction
        case left.isFalse neq =>
          apply rel_sym_acb a b c PG.l1 PG.l2 abc_col
      · intro _
        apply PG.l1 b d
    rw [inter_empty] at b_in_inter
    exact b_in_inter
  · have abp_col :
        ell a b p := by
      apply star_imp_ell a b p a_in_bp
    have pcd_col :
        ell p c d := by
      apply star_imp_ell p c d p_in_cd
    have abc_neq :
        a ≠ b ∧ a ≠ c ∧ b ≠ c := by
      apply ncol_imp_neq (ell := ell) a b c
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
      apply abc_col
      -- ℓ(a, c, b) follows from L₂, now.
      apply rel_sym_acb a c b PG.l1 PG.l2
      apply PG.l2 a c b p
      · exact abp_col
      · apply rel_sym_bca p c b PG.l1 PG.l2 pcd_col
      · exact bp_neq
    have q_ex :
        ∃ q, ell q a c ∧ ell q b d := by
      apply PG.l3 a b c d p
      · apply rel_sym_cab a b p PG.l1 PG.l2 abp_col
      · exact pcd_col
    match q_ex with
    | ⟨q, qac_col, qbd_col⟩ =>
      have q_in_inter :
          q ∈ star ell a c ∩ star ell b d := by
        rw [inter_def]
        simp
        constructor
        · split
          case left.isTrue ac_eq =>
            contradiction
          case left.isFalse _ =>
            apply rel_sym_bca q a c PG.l1 PG.l2 qac_col
        · split
          case right.isTrue bd_eq =>
            contradiction
          case right.isFalse _ =>
            apply rel_sym_bca q b d PG.l1 PG.l2 qbd_col
      rw [inter_empty] at q_in_inter
      exact q_in_inter

theorem p_4
  [ProjectiveGeometry G ell]
  (a b c : G)
  (a_in_bc : a ∈ star ell b c)
  (ab_neq : a ≠ b) :
    c ∈ star ell a b := by
  have inter_nempty :
      star ell a b ∩ star ell c c ≠ ∅ := by
    apply p_3 a c b c a (p_2 a c) a_in_bc ab_neq
  unfold star at inter_nempty
  simp at inter_nempty
  apply inter_nempty

theorem p_5
  [PG : ProjectiveGeometry G ell]
  (a b c : G)
  (a_in_bc : a ∈ star ell b c) :
    star ell a b ⊆ star ell b c := by
  -- We may assume that a ≠ b (and hence b ≠ c) by P₁.
  intro p p_in_ab
  obtain rfl | ab_neq := eq_or_ne a b
  · simp at p_in_ab
    rw [p_in_ab]
    exact a_in_bc
  · obtain rfl | bc_neq := eq_or_ne b c
    · simp at a_in_bc
      contradiction
    · -- In particular, one has c ∈ a ⋆ b by P₄.
      have c_in_ab :
          c ∈ star ell a b := by
        apply p_4 a b c a_in_bc ab_neq
      -- We may assume that p ≠ a and p ≠ c.
      obtain rfl | pa_neq := eq_or_ne p a
      · unfold star at c_in_ab
        simp at c_in_ab
        split at c_in_ab
        · contradiction
        · unfold star
          simp
          split
          · contradiction
          · apply rel_sym_bca p b c PG.l1 PG.l2 c_in_ab
      · obtain rfl | pc_neq := eq_or_ne p c
        · unfold star
          simp
          split
          · rename_i bp_eq
            exact id bp_eq.symm
          · apply rel_sym_bca p b p PG.l1 PG.l2 (PG.l1 p b)
        · have b_in_pa :
              b ∈ star ell p a := by
            apply p_4 p a b p_in_ab pa_neq
          have inter_nempty :
              star ell c p ∩ star ell a a ≠ ∅ := by
            apply p_3 c a p a b c_in_ab b_in_pa (id (Ne.symm pc_neq))
          have a_in_cp :
              a ∈ star ell c p := by
            unfold star at inter_nempty
            simp at inter_nempty
            apply inter_nempty
          have inter_nempty :
              star ell b c ∩ star ell p p ≠ ∅ := by
            apply p_3 b p c p a b_in_pa a_in_cp bc_neq
          unfold star at inter_nempty
          simp at inter_nempty
          apply inter_nempty

theorem p_6
  [ProjectiveGeometry G ell]
  (a b : G) :
    star ell a b = star ell b a := by
  apply eq_of_subset_of_subset
  · apply p_5 a b a (p_2 a b)
  · apply p_5 b a b (p_2 b a)

theorem p_7
  [ProjectiveGeometry G ell]
  (a b c : G)
  (a_in_bc : a ∈ star ell b c)
  (ab_neq : a ≠ b) :
    star ell a b = star ell b c := by
  have c_in_ba :
      c ∈ star ell b a := by
    rw [<- p_6 a b]
    apply p_4 a b c a_in_bc ab_neq
  apply p_5 c b a at c_in_ba
  apply eq_of_subset_of_subset
  · apply p_5 a b c a_in_bc
  · rw [p_6 c b, p_6 b a] at c_in_ba
    exact c_in_ba

theorem p_8
  [ProjectiveGeometry G ell]
  (a b c d : G)
  (a_in_cd : a ∈ star ell c d)
  (b_in_cd : b ∈ star ell c d)
  (ab_neq : a ≠ b) :
    star ell a b = star ell c d := by
    obtain rfl | bc_neq := eq_or_ne b c
    · rw [p_7 a b d a_in_cd ab_neq]
    · rw [<- p_7 b c d b_in_cd bc_neq]
      rw [<- p_7 b c d b_in_cd bc_neq] at a_in_cd
      rw [<- p_7 a b c a_in_cd ab_neq]

theorem p_9
  [PG : ProjectiveGeometry G ell]
  (a b c d p : G)
  (a_in_bp : a ∈ star ell b p)
  (p_in_cd : p ∈ star ell c d) :
    ∃ q : G, q ∈ star ell b d ∧ a ∈ star ell c q := by
  by_cases c_in_bd : c ∈ star ell b d
  · have cd_subseteq_bd :
        star ell c d ⊆ star ell b d := by
      rw [p_6 b d]
      rw [p_6 b d] at c_in_bd
      apply p_5 c d b c_in_bd
    apply cd_subseteq_bd at p_in_cd
    have pb_subseteq_bd :
        star ell p b ⊆ star ell b d := by
      apply p_5 p b d p_in_cd
    rw [p_6 b p] at a_in_bp
    apply pb_subseteq_bd at a_in_bp
    -- Thus one can choose q = a.
    use a
    constructor
    · exact a_in_bp
    · unfold star
      simp
      split
      case h.right.isTrue ca_eq =>
        exact id ca_eq.symm
      case h.right.isFalse ca_neq =>
        apply rel_sym_bca a c a PG.l1 PG.l2 (PG.l1 a c)
  · obtain rfl | ab_eq := eq_or_ne a c
    · -- And if a = c, then one can choose q = b.
      use b
      constructor
      · unfold star
        simp
        intro _
        apply PG.l1 b d
      · unfold star
        simp
        intro _
        apply PG.l1 a b
    · -- So we may assume that c ∉ b ⋆ d and a ≠ c.
      have q_ex :
          ∃ q, q ∈ star ell a c ∩ star ell b d := by
        let inter := star ell a c ∩ star ell b d
        rw [<- nonempty_def]
        have disj :
            inter = ∅ ∨ Set.Nonempty inter :=
          by apply eq_empty_or_nonempty inter
        have inter_nempty :
            inter ≠ ∅ := by
          apply p_3 a b c d p a_in_bp p_in_cd ab_eq
        rcases disj
        case inl _ => contradiction
        case inr nempty => exact nempty
      match q_ex with
      | ⟨q, q_in_ac, q_in_bd⟩ =>
        use q
        constructor
        · exact q_in_bd
        · obtain rfl | qa_neq := eq_or_ne q a
          · unfold star
            simp
            split
            case h.right.inl.isTrue cq_eq =>
              exact id cq_eq.symm
            case h.right.inl.isFalse _ =>
              apply rel_sym_bca q c q PG.l1 PG.l2 (PG.l1 q c)
          · have c_in_qa :
                c ∈ star ell q a := by
              apply p_4 q a c q_in_ac qa_neq
            have cq_neq :
                c ≠ q := by
              intro cq_eq
              rw [cq_eq] at c_in_bd
              exact c_in_bd q_in_bd
            apply p_4 c q a c_in_qa cq_neq

-- set_option diagnostics true
-- set_option diagnostics.threshold 10000

def central_projection
  (a b c z : G)
  (ell : G → G → G → Prop)
  (x : star ell a c) :
    Set (star ell b c) :=
  Subtype.val ⁻¹' (star ell x z ∩ star ell b c)

theorem star_nempty_and_neq_imp_sing
  [PG : ProjectiveGeometry G ell]
  (a b c d : G)
  (nempty : star ell a b ∩ star ell c d ≠ ∅)
  (neq : star ell a b ≠ star ell c d) :
    -- (star ell a b ∩ star ell c d).ncard = 1 := by
    ∃ y, star ell a b ∩ star ell c d = {y} := by
  rw [<- nonempty_iff_ne_empty] at nempty
  rw [nonempty_def] at nempty
  match nempty with
  | ⟨x, x_in_ab, x_in_cd⟩ =>
  -- rw [ncard_eq_one]
  use x
  apply eq_of_subset_of_subset
  · intro y y_in_inter
    simp
    rcases y_in_inter
    rename_i y_in_ab y_in_cd
    -- Supposing x ≠ y will now give (a ⋆ b) = (c ⋆ d) which contradicts
    -- with neq.
    have xy_neq_neq :
        ¬ x ≠ y := by
      intro xy_neq
      have xy_eq_ab :
          star ell x y = star ell a b := by
        apply p_8 x y a b x_in_ab y_in_ab xy_neq
      have xy_eq_cd :
          star ell x y = star ell c d := by
        apply p_8 x y c d x_in_cd y_in_cd xy_neq
      rw [xy_eq_ab] at xy_eq_cd
      apply neq
      exact xy_eq_cd
    simp at xy_neq_neq
    exact id (Eq.symm xy_neq_neq)
  · intro y y_in_x
    simp at y_in_x
    rw [y_in_x]
    exact mem_inter x_in_ab x_in_cd

theorem abc_inter_sing
  [PG : ProjectiveGeometry G ell]
  (a b c : G)
  (abc_ncol : ¬ ell a b c) :
    star ell a b ∩ star ell a c = {a} := by
  apply eq_of_subset_of_subset
  · intro x x_in_inter
    have neq := by apply ncol_imp_neq a b c abc_ncol
    simp
    cases x_in_inter with
    | intro x_in_ab x_in_ac =>
      have ax_neq_neq :
          ¬ a ≠ x := by
        intro ax_neq
        rw [p_6 a b] at x_in_ab
        rw [p_6 a c] at x_in_ac
        have a_in_ba := by apply p_2 (ell := ell) a b
        have a_in_ca := by apply p_2 (ell := ell) a c
        have ax_eq_ba := by apply p_8 (ell := ell) a x b a a_in_ba x_in_ab ax_neq
        have ax_eq_ca := by apply p_8 (ell := ell) a x c a a_in_ca x_in_ac ax_neq
        rw [ax_eq_ca] at ax_eq_ba
        have b_in_ab := by apply p_2 (ell := ell) b a
        rw [p_6 a b] at b_in_ab
        rw [<- ax_eq_ba] at b_in_ab
        simp at b_in_ab
        cases neq with
        | intro _ rest =>
          cases rest with
          | intro ac_neq _ =>
            have cab_col :
                ell c a b := by
              split at b_in_ab
              · rw [b_in_ab]
                apply PG.l1 c a
              · exact b_in_ab
            apply abc_ncol
            apply rel_sym_bca c a b PG.l1 PG.l2 cab_col
      simp at ax_neq_neq
      exact id (Eq.symm ax_neq_neq)
  · intro x x_in_a; simp at x_in_a; rw [x_in_a]
    rw [inter_def]
    simp
    constructor
    · intro _; apply PG.l1 a b
    · intro _; apply PG.l1 a c

theorem cen_proj_sing
  [PG : ProjectiveGeometry G ell]
  (a b c : G)
  (z : star ell a b)
  (x : star ell a c)
  (abc_ncol : ¬ ell a b c)
  (az_neq : a ≠ z)
  (bz_neq : b ≠ z) :
    ∃ y, central_projection a b c z ell x = {y} := by
  have z_nin_ac :
      z.val ∉ star ell a c := by
    have inter_eq_a := by apply abc_inter_sing (ell := ell) a b c abc_ncol
    intro z_in_ac
    let zp := z.property
    have z_in_inter :
        z.val ∈ star ell a b ∩ star ell a c := by
      exact mem_inter zp z_in_ac
    rw [inter_eq_a] at z_in_inter
    exact id (Ne.symm az_neq) z_in_inter
  have z_nin_cb :
      z.val ∉ star ell c b := by
    have bca_ncol :
        ¬ell b c a := by
      intro bca_col
      have abc_col :
          ell a b c := by
        apply rel_sym_cab b c a PG.l1 PG.l2 bca_col
      exact abc_ncol abc_col
    have inter_eq_b := by apply abc_inter_sing (ell := ell) b c a bca_ncol
    intro z_in_cb
    rw [p_6 c b] at z_in_cb
    rw [<- p_6 a b] at inter_eq_b
    let zp := z.property
    have z_in_inter :
        z.val ∈ star ell b c ∩ star ell a b := by
      exact mem_inter z_in_cb zp
    rw [inter_eq_b] at z_in_inter
    exact id (Ne.symm bz_neq) z_in_inter
  -- rw [ncard_eq_one]
  -- (x ⋆ z) ∩ (b ⋆ c) ≠ ∅ by P₃
  have nempty :
      star ell x.val z ∩ star ell c b ≠ ∅ := by
    apply p_3 (ell := ell) x.val c z b a
    · rw [p_6 (ell := ell) c a]
      exact x.property
    · apply p_4
      · rw [p_6 (ell := ell) b a]
        exact z.property
      · exact id (Ne.symm bz_neq)
    · intro xz_eq
      rw [<- xz_eq] at z_nin_ac
      exact z_nin_ac x.property
  unfold central_projection
  rw [p_6 (ell := ell) b c]
  have xz_neq_cb :
      star ell x z ≠ star ell c b := by
    intro xz_eq_cb
    rw [<- xz_eq_cb] at z_nin_cb
    apply z_nin_cb
    apply p_2 z.val x
  have sing := by apply star_nempty_and_neq_imp_sing x.val z.val c b nempty xz_neq_cb
  -- exact ncard_eq_one.mp sing
  match sing with
  | ⟨y, y_in_inter⟩ =>
    have y_in_cb :
        y ∈ star ell c b := by
      apply mem_of_mem_inter_right (a := (star ell x.val z.val))
      rw [y_in_inter]
      exact rfl
    use ⟨y, y_in_cb⟩
    rw [y_in_inter]
    apply eq_of_subset_of_subset
    · simp
    · simp

class CentralProjectionQuadruple
  (ell : G → G → G → Prop)
  (a b c : G)
  (z : star ell a b) where
  abc_ncol : ¬ ell a b c
  az_neq : a ≠ z
  bz_neq : b ≠ z

noncomputable def cen_proj_map
  [PG : ProjectiveGeometry G ell]
  (a b c : G)
  (z : star ell a b)
  [CPQ : CentralProjectionQuadruple ell a b c z]
  (x : star ell a c) :
    star ell b c :=
  Exists.choose (cen_proj_sing (PG := PG) a b c z x CPQ.abc_ncol CPQ.az_neq CPQ.bz_neq)

theorem cen_proj_arg_col
  [PG : ProjectiveGeometry G ell]
  (a b c : G)
  (z : star ell a b)
  [CPQ : CentralProjectionQuadruple ell a b c z]
  (x : star ell a c) :
    ell z x (cen_proj_map (ell := ell) a b c z x) := by
  sorry

instance
  [PG : ProjectiveGeometry G ell]
  [CPQ : CentralProjectionQuadruple ell a b c z] :
    have zp_sym :
        z.val ∈ star ell b a := by
      rw [<- p_6 (ell := ell) a b]
      exact z.property
    CentralProjectionQuadruple ell b a c ⟨z.val, zp_sym⟩ where
  abc_ncol := by
    intro bac_col
    apply CPQ.abc_ncol
    apply rel_sym_bac b a c PG.l1 PG.l2 bac_col
  az_neq := by exact CentralProjectionQuadruple.bz_neq c
  bz_neq := by exact CentralProjectionQuadruple.az_neq c

theorem cen_proj_bij
  [PG : ProjectiveGeometry G ell]
  [CPQ : CentralProjectionQuadruple ell a b c z] :
    Function.Bijective (cen_proj_map (ell := ell) a b c z) := by
  have zp_sym :
      z.val ∈ star ell b a := by
    rw [<- p_6 (ell := ell) a b]
    exact z.property
  let inverse := (cen_proj_map (ell := ell) b a c ⟨z, zp_sym⟩)
  rw [Function.bijective_iff_has_inverse]
  use inverse
  constructor
  · unfold Function.LeftInverse
    intro x
    unfold_let
    sorry
  · sorry

end Basic
