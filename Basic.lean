import Mathlib.Tactic

open Set

namespace Basic

variable [DecidableEq G]

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

-- Let G = (G, ℓ) be a projective geometry. Then the operator ⋆ : G × G →
-- Powerset(G) defined by a ⋆ b := {c ∈ G / ℓ(a, b, c)} if a ≠ b and a ⋆
-- a := {a} satisfies P₁, P₂ and P₃.
@[simp]
def star
  [ProjectiveGeometry G ell]
  (a b : G) :
    Set G :=
  {c : G | if a = b then c = a else ell a b c}

@[simp]
theorem p_1
  [ProjectiveGeometry G ell]
  (a : G) :
    star (ell := ell) a a = {a} := by
  unfold star
  simp

theorem p_2
  [PG : ProjectiveGeometry G ell] :
    ∀ a b, a ∈ star (ell := ell) b a := by
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
      apply rel_sym_bca a b a PG.l1 PG.l2 (PG.l1 a b)

lemma star_imp_ell
  [PG : ProjectiveGeometry G ell]
  (x y z : G)
  (x_in_yz : x ∈ star (ell := ell) y z) :
    ell x y z := by
  obtain rfl | yz_neq := eq_or_ne y z
  · apply rel_sym_bca y x y PG.l1 PG.l2 (PG.l1 y x)
  · unfold star at x_in_yz
    split at x_in_yz
    case inr.inl eq => apply yz_neq at eq; contradiction
    case inr.inr _ =>
      simp at x_in_yz
      apply rel_sym_cab y z x PG.l1 PG.l2 x_in_yz

lemma abc_ncol_imp_neq
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

theorem p_3
  [PG : ProjectiveGeometry G ell]
  (a b c d p : G)
  (a_in_bp : a ∈ star (ell := ell) b p)
  (p_in_cd : p ∈ star (ell := ell) c d)
  (ac_neq : a ≠ c) :
    star (ell := ell) a c ∩ star (ell := ell) b d ≠ ∅ := by
  intro inter_empty
  by_cases abc_col : ell a b c
  · have b_in_inter :
        b ∈ star (ell := ell) a c ∩ star (ell := ell) b d := by
      rw [inter_def]
      simp
      constructor
      · split
        case left.inl eq =>
          apply ac_neq at eq
          contradiction
        case left.inr neq =>
          apply rel_sym_acb a b c PG.l1 PG.l2 abc_col
      · right
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
      apply abc_ncol_imp_neq (ell := ell) a b c
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
          q ∈ star (ell := ell) a c ∩ star (ell := ell) b d := by
        rw [inter_def]
        simp
        constructor
        · split
          case left.inl ac_eq =>
            contradiction
          case left.inr _ =>
            apply rel_sym_bca q a c PG.l1 PG.l2 qac_col
        · split
          case right.inl bd_eq =>
            contradiction
          case right.inr _ =>
            apply rel_sym_bca q b d PG.l1 PG.l2 qbd_col
      rw [inter_empty] at q_in_inter
      exact q_in_inter

theorem p_4
  [ProjectiveGeometry G ell]
  (a b c : G)
  (a_in_bc : a ∈ star (ell := ell) b c)
  (ab_neq : a ≠ b) :
    c ∈ star (ell := ell) a b := by
  have inter_nempty :
      star (ell := ell) a b ∩ star (ell := ell) c c ≠ ∅ := by
    apply p_3 a c b c a (p_2 a c) a_in_bc ab_neq
  unfold star at inter_nempty
  simp at inter_nempty
  apply inter_nempty

theorem p_5
  [PG : ProjectiveGeometry G ell]
  (a b c : G)
  (a_in_bc : a ∈ star (ell := ell) b c) :
    star (ell := ell) a b ⊆ star (ell := ell) b c := by
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
          c ∈ star (ell := ell) a b := by
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
              b ∈ star (ell := ell) p a := by
            apply p_4 p a b p_in_ab pa_neq
          have inter_nempty :
              star (ell := ell) c p ∩ star (ell := ell) a a ≠ ∅ := by
            apply p_3 c a p a b c_in_ab b_in_pa (id (Ne.symm pc_neq))
          have a_in_cp :
              a ∈ star (ell := ell) c p := by
            unfold star at inter_nempty
            simp at inter_nempty
            apply inter_nempty
          have inter_nempty :
              star (ell := ell) b c ∩ star (ell := ell) p p ≠ ∅ := by
            apply p_3 b p c p a b_in_pa a_in_cp bc_neq
          unfold star at inter_nempty
          simp at inter_nempty
          apply inter_nempty

theorem p_6
  [ProjectiveGeometry G ell]
  (a b : G) :
    star (ell := ell) a b = star (ell := ell) b a := by
  apply eq_of_subset_of_subset
  · apply p_5 a b a (p_2 a b)
  · apply p_5 b a b (p_2 b a)

theorem p_7
  [ProjectiveGeometry G ell]
  (a b c : G)
  (a_in_bc : a ∈ star (ell := ell) b c)
  (ab_neq : a ≠ b) :
    star (ell := ell) a b = star (ell := ell) b c := by
  have c_in_ba :
      c ∈ star (ell := ell) b a := by
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
  (a_in_cd : a ∈ star (ell := ell) c d)
  (b_in_cd : b ∈ star (ell := ell) c d)
  (ab_neq : a ≠ b) :
    star (ell := ell) a b = star (ell := ell) c d := by
    obtain rfl | bc_neq := eq_or_ne b c
    · rw [p_7 a b d a_in_cd ab_neq]
    · rw [<- p_7 b c d b_in_cd bc_neq]
      rw [<- p_7 b c d b_in_cd bc_neq] at a_in_cd
      rw [<- p_7 a b c a_in_cd ab_neq]

theorem p_9
  [PG : ProjectiveGeometry G ell]
  (a b c d p : G)
  (a_in_bp : a ∈ star (ell := ell) b p)
  (p_in_cd : p ∈ star (ell := ell) c d) :
    ∃ q : G, q ∈ star (ell := ell) b d ∧ a ∈ star (ell := ell) c q := by
  by_cases c_in_bd : c ∈ star (ell := ell) b d
  · have cd_subseteq_bd :
        star (ell := ell) c d ⊆ star (ell := ell) b d := by
      rw [p_6 b d]
      rw [p_6 b d] at c_in_bd
      apply p_5 c d b c_in_bd
    apply cd_subseteq_bd at p_in_cd
    have pb_subseteq_bd :
        star (ell := ell) p b ⊆ star (ell := ell) b d := by
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
      case h.right.inl ca_eq =>
        exact id ca_eq.symm
      case h.right.inr ca_neq =>
        apply rel_sym_bca a c a PG.l1 PG.l2 (PG.l1 a c)
  · obtain rfl | ab_eq := eq_or_ne a c
    · -- And if a = c, then one can choose q = b.
      use b
      constructor
      · unfold star
        simp
        right
        apply PG.l1 b d
      · unfold star
        simp
        right
        apply PG.l1 a b
    · -- So we may assume that c ∉ b ⋆ d and a ≠ c.
      have q_ex :
          ∃ q, q ∈ star (ell := ell) a c ∩ star (ell := ell) b d := by
        let inter := star (ell := ell) a c ∩ star (ell := ell) b d
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
            case h.right.inl.inl cq_eq =>
              exact id cq_eq.symm
            case h.right.inl.inr _ =>
              apply rel_sym_bca q c q PG.l1 PG.l2 (PG.l1 q c)
          · have c_in_qa :
                c ∈ star (ell := ell) q a := by
              apply p_4 q a c q_in_ac qa_neq
            have cq_neq :
                c ≠ q := by
              intro cq_eq
              rw [cq_eq] at c_in_bd
              exact c_in_bd q_in_bd
            apply p_4 c q a c_in_qa cq_neq

end Basic
