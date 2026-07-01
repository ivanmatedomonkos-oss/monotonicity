import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option linter.unusedSectionVars false

-- ==========================================
-- 1. THE O-MINIMAL EXTERNAL API (GEOMETRY)
-- ==========================================

variable {R : Type} [ConditionallyCompleteLinearOrder R] [DenselyOrdered R]

/-- S_1: Definable subsets of R (Switched to opaque to fix parsing errors) -/
opaque IsDefinable1 : Set R → Prop

/-- S_2: Definable subsets of R^2 -/
opaque IsDefinable2 : Set (R × R) → Prop

-- Structural Boolean & Projection Axioms
axiom def1_compl {A : Set R} (h : IsDefinable1 A) : IsDefinable1 Aᶜ
axiom def1_inter {A B : Set R} (hA : IsDefinable1 A) (hB : IsDefinable1 B) : IsDefinable1 (A ∩ B)
axiom def_proj_x {A : Set (R × R)} (h : IsDefinable2 A) : IsDefinable1 {x | ∃ y, (x, y) ∈ A}
axiom def_proj_y {A : Set (R × R)} (h : IsDefinable2 A) : IsDefinable1 {y | ∃ x, (x, y) ∈ A}

-- Base Geometric Assumptions (f and I are parameterized explicitly to prevent scoping errors)
axiom interval_definable (c d : R) : IsDefinable1 (Set.Ioo c d)
axiom f_less_than_const_definable (f : R → R) (c : R) : IsDefinable1 {y | f y < c}
axiom o_minimal_interval {A : Set R} (h_def : IsDefinable1 A) (h_inf : Set.Infinite A) :
  ∃ c d, c < d ∧ Set.Ioo c d ⊆ A

-- ==========================================
-- 2. LOCAL FORMULAS (PURE LOGIC)
-- ==========================================

def PhiPlusPlus (f : R → R) (I : Set R) (x : R) : Prop :=
  x ∈ I ∧ ∃ c1 ∈ I, ∃ c2 ∈ I, c1 < x ∧ x < c2 ∧
    (∀ y ∈ I, c1 < y → y < x → f y > f x) ∧
    (∀ y ∈ I, x < y → y < c2 → f y > f x)

def PhiPlusMinus (f : R → R) (I : Set R) (x : R) : Prop :=
  x ∈ I ∧ ∃ c1 ∈ I, ∃ c2 ∈ I, c1 < x ∧ x < c2 ∧
    (∀ y ∈ I, c1 < y → y < x → f y > f x) ∧
    (∀ y ∈ I, x < y → y < c2 → f y < f x)

def PhiMinusPlus (f : R → R) (I : Set R) (x : R) : Prop :=
  x ∈ I ∧ ∃ c1 ∈ I, ∃ c2 ∈ I, c1 < x ∧ x < c2 ∧
    (∀ y ∈ I, c1 < y → y < x → f y < f x) ∧
    (∀ y ∈ I, x < y → y < c2 → f y > f x)

def PhiMinusMinus (f : R → R) (I : Set R) (x : R) : Prop :=
  x ∈ I ∧ ∃ c1 ∈ I, ∃ c2 ∈ I, c1 < x ∧ x < c2 ∧
    (∀ y ∈ I, c1 < y → y < x → f y < f x) ∧
    (∀ y ∈ I, x < y → y < c2 → f y < f x)

def PsiPlusMinus (f : R → R) (I : Set R) (v : R) : Prop :=
  v ∈ I ∧ ∃ v1 ∈ I, ∃ v2 ∈ I, v1 < v ∧ v < v2 ∧ 
    ∀ z1 ∈ I, ∀ z2 ∈ I, v1 < z1 → z1 < v → v < z2 → z2 < v2 → f z1 > f z2

def PsiMinusPlus (f : R → R) (I : Set R) (v : R) : Prop :=
  v ∈ I ∧ ∃ u1 ∈ I, ∃ u2 ∈ I, u1 < v ∧ v < u2 ∧ 
    ∀ z1 ∈ I, ∀ z2 ∈ I, u1 < z1 → z1 < v → v < z2 → z2 < u2 → f z1 < f z2

-- ==========================================
-- 3. STEP 1: PARTITIONING & A_x DEFINABILITY
-- ==========================================

def A_x (f : R → R) (a x : R) : Set R := Set.Ioo a x ∩ { y | f y < f x }

theorem A_x_is_definable (f : R → R) (a x : R) : IsDefinable1 (A_x f a x) := by
  exact def1_inter (interval_definable a x) (f_less_than_const_definable f (f x))

-- Aligned the return types of Set.Ioo c d to match the expected lemma inputs
lemma step_1_partition (f : R → R) {a b : R} (hab : a < b) 
  (hinj : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, f x = f y → x = y) :
  ∃ c d, c < d ∧ Set.Ioo c d ⊆ Set.Ioo a b ∧ 
  ( (∀ x ∈ Set.Ioo c d, PhiPlusPlus f (Set.Ioo c d) x) ∨ 
    (∀ x ∈ Set.Ioo c d, PhiPlusMinus f (Set.Ioo c d) x) ∨ 
    (∀ x ∈ Set.Ioo c d, PhiMinusPlus f (Set.Ioo c d) x) ∨ 
    (∀ x ∈ Set.Ioo c d, PhiMinusMinus f (Set.Ioo c d) x) ) := by
  sorry

-- ==========================================
-- 4. STEP 2: EASY CASES & S(x) DEFINABILITY
-- ==========================================

axiom V_S_is_definable (f : R → R) (x : R) : IsDefinable2 { p : R × R | x < p.1 ∧ p.1 ≤ p.2 ∧ f p.1 ≤ f x }

def S_x (f : R → R) (x b : R) : Set R :=
  Set.Ioo x b ∩ { s | ∃ y, (y, s) ∈ { p : R × R | x < p.1 ∧ p.1 ≤ p.2 ∧ f p.1 ≤ f x } }ᶜ

theorem S_x_is_definable (f : R → R) (x b : R) : IsDefinable1 (S_x f x b) := by
  have h_proj := def_proj_y (V_S_is_definable f x)
  exact def1_inter (interval_definable x b) (def1_compl h_proj)

lemma step_2_easy_case_minus_plus (f : R → R) {c d : R} (hcd : c < d) 
  (h_phi : ∀ x ∈ Set.Ioo c d, PhiMinusPlus f (Set.Ioo c d) x) :
  StrictMonoOn f (Set.Ioo c d) := by
  sorry

-- ==========================================
-- 5. STEP 3: DIFFICULT CASES & B DEFINABILITY
-- ==========================================

axiom V_B_is_definable (f : R → R) (I : Set R) : IsDefinable2 { p : R × R | p.2 ∈ I ∧ p.2 > p.1 ∧ f p.2 ≤ f p.1 }
axiom I_is_definable (I : Set R) : IsDefinable1 I

def B_set (f : R → R) (I : Set R) : Set R :=
  I ∩ { x | ∃ y, (x, y) ∈ { p : R × R | p.2 ∈ I ∧ p.2 > p.1 ∧ f p.2 ≤ f p.1 } }ᶜ

theorem B_is_definable (f : R → R) (I : Set R) : IsDefinable1 (B_set f I) := by
  have h_proj := def_proj_x (V_B_is_definable f I)
  exact def1_inter (I_is_definable I) (def1_compl h_proj)

lemma psi_contradiction (f : R → R) (I : Set R) (v : R) 
  (h_I_convex : ∀ x y z, x ∈ I → y ∈ I → x ≤ z → z ≤ y → z ∈ I) 
  (h_pm : PsiPlusMinus f I v) (h_mp : PsiMinusPlus f I v) : False := by
  rcases h_pm with ⟨hvI, v1, hv1_I, v2, hv2_I, hv1_lt, hlt_v2, H_pm⟩
  rcases h_mp with ⟨_, u1, hu1_I, u2, hu2_I, hu1_lt, hlt_u2, H_mp⟩
  
  have h_max_lt : max v1 u1 < v := max_lt hv1_lt hu1_lt
  rcases exists_between h_max_lt with ⟨z1, hz1_left, hz1_right⟩
  
  have h_max_I : max v1 u1 ∈ I := by
    rcases le_total v1 u1 with hle | hle
    · rw [max_eq_right hle]; exact hu1_I
    · rw [max_eq_left hle]; exact hv1_I
    
  have hz1_I : z1 ∈ I := h_I_convex (max v1 u1) v z1 h_max_I hvI (le_of_lt hz1_left) (le_of_lt hz1_right)
  
  have h_lt_min : v < min v2 u2 := lt_min hlt_v2 hlt_u2
  rcases exists_between h_lt_min with ⟨z2, hz2_left, hz2_right⟩
  
  have h_min_I : min v2 u2 ∈ I := by
    rcases le_total v2 u2 with hle | hle
    · rw [min_eq_left hle]; exact hv2_I
    · rw [min_eq_right hle]; exact hu2_I
    
  have hz2_I : z2 ∈ I := h_I_convex v (min v2 u2) z2 hvI h_min_I (le_of_lt hz2_left) (le_of_lt hz2_right)
  
  have h_gt := H_pm z1 hz1_I z2 hz2_I
    (lt_of_le_of_lt (le_max_left v1 u1) hz1_left) hz1_right
    hz2_left (lt_of_lt_of_le hz2_right (min_le_left v2 u2))
    
  have h_lt := H_mp z1 hz1_I z2 hz2_I
    (lt_of_le_of_lt (le_max_right v1 u1) hz1_left) hz1_right
    hz2_left (lt_of_lt_of_le hz2_right (min_le_right v2 u2))
    
  exact lt_irrefl (f z1) (lt_trans h_lt h_gt)

lemma step_3_difficult_case_plus_plus_impossible (f : R → R) {c d : R} (hcd : c < d)
  (h_phi : ∀ x ∈ Set.Ioo c d, PhiPlusPlus f (Set.Ioo c d) x) :
  False := by
  sorry

-- ==========================================
-- 6. ASSEMBLY: LEMMA 2
-- ==========================================

theorem lemma_2_injective_implies_strictly_monotone_on_subinterval
  (f : R → R) {a b : R} (hab : a < b) (hinj : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, f x = f y → x = y) :
  ∃ c d, c < d ∧ Set.Ioo c d ⊆ Set.Ioo a b ∧
  (StrictMonoOn f (Set.Ioo c d) ∨ StrictAntiOn f (Set.Ioo c d)) := by
  
  have ⟨c, d, hcd, hsub, h_cases⟩ := step_1_partition f hab hinj
  
  rcases h_cases with h_pp | h_pm | h_mp | h_mm
  
  · exfalso
    exact step_3_difficult_case_plus_plus_impossible f hcd h_pp
    
  · use c, d
    refine ⟨hcd, hsub, Or.inr ?_⟩
    sorry 
    
  · use c, d
    refine ⟨hcd, hsub, Or.inl ?_⟩
    exact step_2_easy_case_minus_plus f hcd h_mp
    
  · exfalso
    sorry