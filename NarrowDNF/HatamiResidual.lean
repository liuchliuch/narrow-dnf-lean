import NarrowDNF.Fourier
import NarrowDNF.ConditionalExpectation
import NarrowDNF.AdaptiveShift
import NarrowDNF.HatamiActivation

/-!
# Hatami's actual restricted-activation conditional components

This file formalizes the Step III/IV construction using actual adaptive atom
labels. `approxComponent` is conditional expectation onto the family retaining
only activations whose index is contained in the component's support. Generic
projection and diagonal estimates are proved here. Construction-specific
cross-term bounds are stated only when proved; no analytic estimate is an axiom.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiResidual

open ProductMeasure
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hatami's family `J_S`: retain exactly the original activations indexed inside `S`. -/
def restrict (J : Activation ι) (S : Finset ι) : Activation ι where
  fires T x := T ⊆ S ∧ J.fires T x
  locality T x y hxy := and_congr_right fun _ => J.locality T x y hxy

omit [Fintype ι] [DecidableEq ι] in
theorem restrict_active_subset (J : Activation ι) (S : Finset ι) (x : Cube ι) :
    (restrict J S).active x ⊆ (S : Set ι) := by
  rintro i ⟨T,hi,hT⟩
  exact hT.1 hi

omit [Fintype ι] [DecidableEq ι] in
theorem restrict_active_subset_original (J : Activation ι) (S : Finset ι) (x : Cube ι) :
    (restrict J S).active x ⊆ J.active x := by
  rintro i ⟨T,hi,hT⟩
  exact ⟨T,hi,hT.2⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The restricted adaptive partition is genuinely coarser than the original one. -/
theorem restrict_sameAtom (J : Activation ι) (S : Finset ι) {x y : Cube ι}
    (hxy : J.SameAtom x y) : (restrict J S).SameAtom x y := by
  apply Activation.sameAtom_of_active_subset_of_agree
    (B := J.active x) (restrict_active_subset_original J S x)
  · rw [hxy.1]
    exact restrict_active_subset_original J S y
  · exact hxy.2

omit [Fintype ι] [DecidableEq ι] in
/-- Agreement on `S` fixes the entire `J_S` adaptive atom. -/
theorem restrict_sameAtom_of_agree (J : Activation ι) (S : Finset ι) {x y : Cube ι}
    (hxy : ∀ i ∈ S, x i = y i) : (restrict J S).SameAtom x y :=
  Activation.sameAtom_of_active_subset_of_agree
    (restrict_active_subset J S x) (restrict_active_subset J S y) hxy

omit [Fintype ι] [DecidableEq ι] in
/-- Any local activation has constant firing status on its own adaptive atoms. -/
theorem fires_congr_atom (J : Activation ι) (T : Finset ι) {x y : Cube ι}
    (hxy : J.SameAtom x y) : J.fires T x ↔ J.fires T y := by
  constructor
  · intro hx
    apply (J.locality T x y ?_).mp hx
    intro i hi
    exact hxy.2 i (Activation.mem_active_of_fires hx hi)
  · intro hy
    apply (J.locality T y x ?_).mp hy
    intro i hi
    have hiy := Activation.mem_active_of_fires hy hi
    have hix : i ∈ J.active x := hxy.1 ▸ hiy
    exact (hxy.2 i hix).symm

/-- Real-valued conditional expectation on the actual full adaptive partition. -/
def adaptiveConditional (p : ℝ) (J : Activation ι) (F : Cube ι → ℝ) : Cube ι → ℝ :=
  ConditionalExpectation.conditional (ConditionalExpectation.adaptiveCode J) (weight p) F

/-- Hatami's `F̃_S = E[F_S | F_(J_S)]`, with actual labels and the exact restricted family. -/
def approxComponent (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S : Finset ι) : Cube ι → ℝ :=
  adaptiveConditional p (restrict J S) (Fourier.component p f S)

/-- The retained Fourier polynomial. -/
def truncated (p : ℝ) (f : Cube ι → ℝ) (retained : Finset (Finset ι)) (x : Cube ι) : ℝ :=
  ∑ S ∈ retained, Fourier.component p f S x

/-- The measurable competitor used in Hatami's Step III. -/
def approxTruncated (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (retained : Finset (Finset ι)) (x : Cube ι) : ℝ :=
  ∑ S ∈ retained, approxComponent p J f S x

theorem approxComponent_locality (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S : Finset ι) (x y : Cube ι) (hxy : ∀ i ∈ S, x i = y i) :
    approxComponent p J f S x = approxComponent p J f S y := by
  apply ConditionalExpectation.conditional_eq_of_atom_eq
  exact (ConditionalExpectation.adaptiveCode_eq_iff _ x y).mpr
    (restrict_sameAtom_of_agree J S hxy)

theorem approxComponent_measurable (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S : Finset ι) (x y : Cube ι) (hxy : J.SameAtom x y) :
    approxComponent p J f S x = approxComponent p J f S y := by
  apply ConditionalExpectation.conditional_eq_of_atom_eq
  exact (ConditionalExpectation.adaptiveCode_eq_iff _ x y).mpr (restrict_sameAtom J S hxy)

theorem approxTruncated_measurable (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (retained : Finset (Finset ι)) (x y : Cube ι) (hxy : J.SameAtom x y) :
    approxTruncated p J f retained x = approxTruncated p J f retained y := by
  apply Finset.sum_congr rfl
  intro S _
  exact approxComponent_measurable p J f S x y hxy

/-- Equation (12): the restricted-component competitor is a valid full-atom readout. -/
theorem adaptive_projection_le_competitor {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (retained : Finset (Finset ι)) :
    ConditionalExpectation.squaredError (weight p) (truncated p f retained)
      (adaptiveConditional p J (truncated p f retained)) ≤
    ConditionalExpectation.squaredError (weight p) (truncated p f retained)
      (approxTruncated p J f retained) := by
  apply ConditionalExpectation.squaredError_minimal_of_measurable
    (ConditionalExpectation.adaptiveCode J) (weight p) _ _ (weight_pos hp0 hp1)
  intro x y hxy
  exact approxTruncated_measurable p J f retained x y
    ((ConditionalExpectation.adaptiveCode_eq_iff J x y).mp hxy)

section Generic
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

omit [Fintype β] in
/-- A conditional expectation fixes a function constant on the realized atom. -/
theorem conditional_eq_of_constant_on_atom (φ : α → β) (w F : α → ℝ)
    (hw : ∀ a, 0 < w a) (x : α) (hF : ∀ y, φ y = φ x → F y = F x) :
    ConditionalExpectation.conditional φ w F x = F x := by
  have hmoment : ConditionalExpectation.moment φ w F (φ x) =
      F x * ConditionalExpectation.mass φ w (φ x) := by
    unfold ConditionalExpectation.moment ConditionalExpectation.mass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [hF y y.property]
    ring
  unfold ConditionalExpectation.conditional ConditionalExpectation.mean
  rw [hmoment]
  exact mul_div_cancel_right₀ _ (ConditionalExpectation.mass_pos φ w hw x).ne'

/-- Weighted squared-error triangle inequality with the sharp elementary factor two. -/
theorem squaredError_triangle_two (w F G H : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ConditionalExpectation.squaredError w F H ≤
      2 * ConditionalExpectation.squaredError w F G +
        2 * ConditionalExpectation.squaredError w G H := by
  unfold ConditionalExpectation.squaredError
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have h : (F a - H a)^2 ≤ 2 * (F a-G a)^2 + 2 * (G a-H a)^2 := by
    nlinarith [sq_nonneg (F a - 2*G a + H a)]
  have hm := mul_le_mul_of_nonneg_left h (hw a)
  nlinarith

end Generic

/-- When the support itself fires, its actual labels determine the component exactly. -/
theorem approxComponent_eq_of_fires {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (S : Finset ι) (x : Cube ι)
    (hx : J.fires S x) : approxComponent p J f S x = Fourier.component p f S x := by
  apply conditional_eq_of_constant_on_atom _ _ _ (weight_pos hp0 hp1)
  intro y hy
  have hxy := (ConditionalExpectation.adaptiveCode_eq_iff (restrict J S) y x).mp hy
  apply Fourier.component_locality
  intro i hi
  have hix : i ∈ (restrict J S).active x :=
    Activation.mem_active_of_fires (show (restrict J S).fires S x from ⟨Finset.Subset.refl S,hx⟩) hi
  have hiy : i ∈ (restrict J S).active y := hxy.1 ▸ hix
  exact hxy.2 i hiy

/-- The competitor that keeps the component only when its complete support is revealed. -/
def revealedComponent (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S : Finset ι) (x : Cube ι) : ℝ :=
  if J.fires S x then Fourier.component p f S x else 0

theorem revealedComponent_measurable (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S : Finset ι) (x y : Cube ι) (hxy : (restrict J S).SameAtom x y) :
    revealedComponent p J f S x = revealedComponent p J f S y := by
  have hfire : J.fires S x ↔ J.fires S y := by
    simpa only [restrict, Finset.Subset.refl, true_and] using fires_congr_atom (restrict J S) S hxy
  unfold revealedComponent
  by_cases hx : J.fires S x
  · rw [if_pos hx, if_pos (hfire.mp hx)]
    apply Fourier.component_locality
    intro i hi
    exact hxy.2 i (Activation.mem_active_of_fires
      (show (restrict J S).fires S x from ⟨Finset.Subset.refl S,hx⟩) hi)
  · rw [if_neg hx, if_neg (fun hy => hx (hfire.mpr hy))]

/-- The diagonal residual is bounded by component energy where its support does not fire. -/
theorem diagonal_residual_le_inactive {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (S : Finset ι) :
    ConditionalExpectation.squaredError (weight p) (Fourier.component p f S)
      (approxComponent p J f S) ≤
      expectation p (fun x => if J.fires S x then 0 else Fourier.component p f S x ^ 2) := by
  have h := ConditionalExpectation.squaredError_minimal_of_measurable
    (ConditionalExpectation.adaptiveCode (restrict J S)) (weight p)
    (Fourier.component p f S) (revealedComponent p J f S) (weight_pos hp0 hp1)
    (fun x y hxy => revealedComponent_measurable p J f S x y
      ((ConditionalExpectation.adaptiveCode_eq_iff (restrict J S) x y).mp hxy))
  apply h.trans_eq
  unfold ConditionalExpectation.squaredError expectation
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : J.fires S x <;> simp [revealedComponent, hx]

/-- Step IV's projection/triangle argument, before substituting the analytic estimates. -/
theorem final_residual_le_two_errors {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (retained : Finset (Finset ι)) :
    ConditionalExpectation.squaredError (weight p) f (adaptiveConditional p J f) ≤
      2 * ConditionalExpectation.squaredError (weight p) f (truncated p f retained) +
      2 * ConditionalExpectation.squaredError (weight p) (truncated p f retained)
        (approxTruncated p J f retained) := by
  apply le_trans (ConditionalExpectation.squaredError_minimal_of_measurable
    (ConditionalExpectation.adaptiveCode J) (weight p) f (approxTruncated p J f retained)
    (weight_pos hp0 hp1) (fun x y hxy => approxTruncated_measurable p J f retained x y
      ((ConditionalExpectation.adaptiveCode_eq_iff J x y).mp hxy)))
  exact squaredError_triangle_two _ _ _ _ (weight_nonneg hp0.le hp1.le)

/-- The exact Step IV numerical implication. Its two norm hypotheses are explicit
and must be discharged for the same retained family and the same activation family. -/
theorem final_residual_le_ten {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (retained : Finset (Finset ι)) (ε0 : ℝ)
    (htrunc : ConditionalExpectation.squaredError (weight p) f (truncated p f retained) ≤ 2*ε0)
    (happrox : ConditionalExpectation.squaredError (weight p) (truncated p f retained)
      (approxTruncated p J f retained) ≤ 3*ε0) :
    ConditionalExpectation.squaredError (weight p) f (adaptiveConditional p J f) ≤ 10*ε0 := by
  have h := final_residual_le_two_errors hp0 hp1 J f retained
  linarith


/-- The Bernoulli mass times the absolute normalized bit is independent of that bit. -/
theorem bitWeight_abs_standardBit {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    bitWeight p b * |Fourier.standardBit p b| = Real.sqrt (p * (1-p)) := by
  have hspos := Real.sqrt_pos.mpr (mul_pos hp0 (sub_pos.mpr hp1))
  have hs := ne_of_gt hspos
  have hs2 := Real.sq_sqrt (le_of_lt (mul_pos hp0 (sub_pos.mpr hp1)))
  cases b <;>
    simp only [bitWeight, Fourier.standardBit, Bool.false_eq_true, ↓reduceIte,
      abs_div, abs_neg, abs_of_pos hp0, abs_of_pos (sub_pos.mpr hp1), abs_of_pos hspos]
  all_goals field_simp
  all_goals nlinarith

/-- The local mass times the absolute component is constant throughout its local cube. -/
theorem component_mass_abs {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (S : Finset ι) (x : Cube ι) :
    HatamiActivation.localMass p S x * |Fourier.component p f S x| =
      Real.sqrt (p * (1-p)) ^ S.card * |Fourier.setCoefficient p f S| := by
  unfold HatamiActivation.localMass weight Fourier.component
  rw [abs_mul, Fourier.setCharacter_eq_prod, Finset.abs_prod]
  dsimp only
  rw [Finset.prod_coe_sort S (fun i => bitWeight p (x i))]
  calc
    _ = (∏ i ∈ S, bitWeight p (x i) * |Fourier.standardBit p (x i)|) *
        |Fourier.setCoefficient p f S| := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by simp_rw [bitWeight_abs_standardBit hp0 hp1]; simp

section GenericBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

omit [Fintype β] in
/-- A finite atom average of a constant-mass absolute function is at most the
ambient point count times its absolute value at the current point. -/
theorem conditional_abs_le_card_mul (φ : α → β) (w F : α → ℝ)
    (hw : ∀ a, 0 < w a) (C : ℝ) (hC : ∀ a, w a * |F a| = C) (x : α) :
    |ConditionalExpectation.conditional φ w F x| ≤ (Fintype.card α : ℝ) * |F x| := by
  have hC0 : 0 ≤ C := by rw [← hC x]; exact mul_nonneg (hw x).le (abs_nonneg _)
  have hmoment : |ConditionalExpectation.moment φ w F (φ x)| ≤ (Fintype.card α : ℝ) * C := by
    rw [ConditionalExpectation.moment_eq_indicator_sum]
    calc
      _ ≤ ∑ y : α, |if φ y = φ x then w y * F y else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y : α, C := by
        apply Finset.sum_le_sum
        intro y _
        by_cases hy : φ y = φ x
        · simp only [if_pos hy, abs_mul, abs_of_pos (hw y)]
          exact (hC y).le
        · simpa [hy] using hC0
      _ = _ := by simp
  have hmass : w x ≤ ConditionalExpectation.mass φ w (φ x) := by
    unfold ConditionalExpectation.mass
    exact Finset.single_le_sum (f := fun y : {a // φ a = φ x} => w y)
      (fun y _ => (hw y).le) (Finset.mem_univ (⟨x,rfl⟩ : {a // φ a = φ x}))
  unfold ConditionalExpectation.conditional ConditionalExpectation.mean
  rw [abs_div, abs_of_pos (ConditionalExpectation.mass_pos φ w hw x)]
  apply (div_le_iff₀ (ConditionalExpectation.mass_pos φ w hw x)).mpr
  apply hmoment.trans
  calc
    (Fintype.card α : ℝ) * C = ((Fintype.card α : ℝ) * |F x|) * w x := by
      rw [← hC x]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

end GenericBound

/-- Hatami's pointwise `2^|S|` conditional-component bound, proved for the actual
restricted adaptive atoms and the local Bernoulli marginal. -/
theorem approxComponent_abs_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (S : Finset ι) (x : Cube ι) :
    |approxComponent p J f S x| ≤ (2 : ℝ)^S.card * |Fourier.component p f S x| := by
  have hφ : ∀ x y : Cube ι, (∀ i, i ∈ S → x i = y i) →
      ConditionalExpectation.adaptiveCode (restrict J S) x =
      ConditionalExpectation.adaptiveCode (restrict J S) y := by
    intro x y hxy
    exact (ConditionalExpectation.adaptiveCode_eq_iff _ x y).mpr
      (restrict_sameAtom_of_agree J S hxy)
  unfold approxComponent adaptiveConditional
  rw [ConditionalExpectation.conditional_localization p (fun i => i ∈ S) _ hφ _
    (Fourier.component_locality p f S) x]
  have h := conditional_abs_le_card_mul
    (fun z : S → Bool => ConditionalExpectation.adaptiveCode (restrict J S)
      (extendFalse (fun i => i ∈ S) z))
    (weight p) (fun z : S → Bool => Fourier.component p f S (extendFalse (fun i => i ∈ S) z))
    (weight_pos hp0 hp1)
    (Real.sqrt (p * (1-p)) ^ S.card * |Fourier.setCoefficient p f S|)
    (fun z => by
      have hm : HatamiActivation.localMass p S (extendFalse (fun i => i ∈ S) z) = weight p z := by
        unfold HatamiActivation.localMass
        congr 1
        funext i
        simp [extendFalse, i.property]
      simpa only [hm] using component_mass_abs hp0 hp1 f S (extendFalse (fun i => i ∈ S) z))
    (fun i => x i)
  have hlocal : Fourier.component p f S (extendFalse (fun i => i ∈ S) (fun i => x i)) =
      Fourier.component p f S x := by
    apply Fourier.component_locality
    intro i hi
    simp [extendFalse, hi]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Nat.cast_pow,
    Nat.cast_ofNat, hlocal] at h
  rw [Subsingleton.elim (Finset.Subtype.fintype S) (Subtype.fintype (fun i => i ∈ S))] at h
  exact h


/-- The exact activation coverage converts diagonal error into the small-component mass. -/
theorem diagonal_residual_le_small_component {p k δ η : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ)
    (S : Finset ι) (hS : S ∈ HatamiActivation.significantSets p f k η) :
    ConditionalExpectation.squaredError (weight p) (Fourier.component p f S)
      (approxComponent p (HatamiActivation.fourierActivation k p δ η f) f S) ≤
      expectation p (fun x => if |Fourier.component p f S x| ≤ η then
        Fourier.component p f S x ^ 2 else 0) := by
  apply (diagonal_residual_le_inactive hp0 hp1 _ f S).trans
  apply expectation_mono hp0.le hp1.le
  intro x
  by_cases hx : (HatamiActivation.fourierActivation k p δ η f).fires S x
  · simp only [if_pos hx]
    split_ifs <;> positivity
  · have hsmall := HatamiActivation.component_lt_of_not_fires hp0.le hp1.le hδ f S x hS hx
    simp [hx, hsmall.le]

/-- Finite-subfamily linearity of product expectation. -/
theorem expectation_finset_sum {κ : Type*} (p : ℝ) (s : Finset κ)
    (F : κ → Cube ι → ℝ) :
    expectation p (fun x => ∑ j ∈ s, F j x) = ∑ j ∈ s, expectation p (F j) := by
  unfold expectation
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- All diagonal terms are controlled by the exact low-degree small-component quantity
which appears in Bourgain's Step II; its analytic estimate remains a separate input. -/
theorem sum_diagonal_le_small_mass {p k δ η : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ) :
    (∑ S ∈ HatamiActivation.significantSets p f k η,
      ConditionalExpectation.squaredError (weight p) (Fourier.component p f S)
        (approxComponent p (HatamiActivation.fourierActivation k p δ η f) f S)) ≤
      expectation p (fun x =>
        ∑ S ∈ Finset.univ.filter (fun S : Finset ι => (S.card : ℝ) ≤ k),
          if |Fourier.component p f S x| ≤ η then Fourier.component p f S x ^ 2 else 0) := by
  rw [expectation_finset_sum]
  calc
    _ ≤ ∑ S ∈ HatamiActivation.significantSets p f k η,
        expectation p (fun x => if |Fourier.component p f S x| ≤ η then
          Fourier.component p f S x ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro S hS
      exact diagonal_residual_le_small_component hp0 hp1 hδ f S hS
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro S hS
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, HatamiActivation.significantSets_card p f k η S hS⟩
      · intro S _ _
        apply expectation_nonneg hp0.le hp1.le
        intro x
        split_ifs <;> positivity

omit [Fintype ι] in
/-- Averaging outside the coordinates read by a local function leaves it unchanged. -/
theorem coordinateMean_eq_of_local (p : ℝ) (T : Finset ι) (G : Cube ι → ℝ)
    (hG : ∀ x y, (∀ j ∈ T, x j = y j) → G x = G y) (i : ι) (hi : i ∉ T)
    (x : Cube ι) : Fourier.coordinateMean p G i x = G x := by
  have hupdate (b : Bool) : G (Function.update x i b) = G x := by
    apply hG
    intro j hj
    have hji : j ≠ i := by
      intro hji
      apply hi
      simpa only [hji] using hj
    exact Function.update_of_ne hji b x
  unfold Fourier.coordinateMean
  rw [hupdate, hupdate]
  ring

/-- A generalized Walsh component averages to zero in each coordinate of its support. -/
theorem coordinateMean_component_zero (p : ℝ) (f : Cube ι → ℝ) (S : Finset ι)
    (i : ι) (hi : i ∈ S) (x : Cube ι) :
    Fourier.coordinateMean p (Fourier.component p f S) i x = 0 := by
  calc
    _ = Fourier.setCoefficient p f S * Fourier.coordinateMean p (Fourier.setCharacter p S) i x := by
      unfold Fourier.coordinateMean Fourier.component
      ring
    _ = 0 := by
      unfold Fourier.setCharacter
      rw [Fourier.coordinateMean_character]
      simp [Fourier.maskEquivFinset, hi]

/-- A component is orthogonal to every local function missing one of its coordinates. -/
theorem component_orthogonal_of_not_subset (p : ℝ) (f : Cube ι → ℝ) (S T : Finset ι)
    (hST : ¬ S ⊆ T) (G : Cube ι → ℝ)
    (hG : ∀ x y, (∀ j ∈ T, x j = y j) → G x = G y) :
    expectation p (fun x => Fourier.component p f S x * G x) = 0 := by
  obtain ⟨i,hiS,hiT⟩ := Finset.not_subset.mp hST
  have h := Fourier.coordinateMean_selfAdjoint p (Fourier.component p f S) G i
  simp_rw [coordinateMean_component_zero p f S i hiS,
    coordinateMean_eq_of_local p T G hG i hiT] at h
  simpa using h.symm

/-- The cross component/conditional-component terms vanish for incomparable supports. -/
theorem component_approx_orthogonal (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S T : Finset ι) (hST : ¬ S ⊆ T) :
    expectation p (fun x => Fourier.component p f S x * approxComponent p J f T x) = 0 :=
  component_orthogonal_of_not_subset p f S T hST _ (approxComponent_locality p J f T)


/-- Corrected global L1 bound for the conditional components. -/
theorem approxComponent_abs_mean_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → Bool) (S : Finset ι) :
    expectation p (fun x => |approxComponent p J (fun y => Influence.boolValue (f y)) S x|) ≤
      (2 : ℝ)^(3*S.card) * p^S.card := by
  let F := fun x => Influence.boolValue (f x)
  let A := 2 * Real.sqrt (p * (1-p))
  have hA0 : 0 ≤ A := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hcoeff : |Fourier.setCoefficient p F S| ≤ A^S.card :=
    Fourier.setCoefficient_bool_abs_le hp0 hp1 f S
  have hcomponent : expectation p (fun x => |Fourier.component p F S x|) =
      |Fourier.setCoefficient p F S| * A^S.card := by
    simp only [Fourier.component, abs_mul]
    rw [expectation_const_mul]
    change |Fourier.setCoefficient p F S| *
      expectation p (fun x => |Fourier.character p (Fourier.maskEquivFinset.symm S) x|) = _
    rw [Fourier.character_abs_mean hp0 hp1, Fourier.degree_maskEquivFinset_symm]
  calc
    _ ≤ expectation p (fun x => (2:ℝ)^S.card * |Fourier.component p F S x|) :=
      expectation_mono hp0.le hp1.le (approxComponent_abs_le hp0 hp1 J F S)
    _ = (2:ℝ)^S.card * (|Fourier.setCoefficient p F S| * A^S.card) := by
      rw [expectation_const_mul, hcomponent]
    _ ≤ (2:ℝ)^S.card * (A^S.card * A^S.card) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hA0 _)) (by positivity)
    _ = (8 * (p * (1-p)))^S.card := by
      have hbase : 2 * A * A = 8 * (p * (1-p)) := by
        dsimp [A]
        nlinarith [Real.sq_sqrt (le_of_lt (mul_pos hp0 (sub_pos.mpr hp1)))]
      rw [← hbase]
      simp only [mul_pow]
      ring
    _ ≤ (8 * p)^S.card := by
      apply pow_le_pow_left₀ (mul_nonneg (by norm_num) (mul_nonneg hp0.le (sub_nonneg.mpr hp1.le)))
      nlinarith [sq_nonneg p]
    _ = (2:ℝ)^(3*S.card) * p^S.card := by
      rw [mul_pow, pow_mul]
      norm_num

section GenericMeanBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

omit [Fintype β] in
/-- The absolute numerator of an atom average is bounded by the global L1 mass. -/
theorem abs_moment_le_abs_sum (φ : α → β) (w F : α → ℝ) (hw : ∀ a, 0 ≤ w a) (b : β) :
    |ConditionalExpectation.moment φ w F b| ≤ ∑ a, w a * |F a| := by
  rw [ConditionalExpectation.moment_eq_indicator_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : φ a = b
  · simp [ha, abs_mul, abs_of_nonneg (hw a)]
  · simpa [ha] using mul_nonneg (hw a) (abs_nonneg (F a))

omit [Fintype β] in
/-- A local atom's positive mass converts a global L1 bound into a conditional bound. -/
theorem abs_mean_le_div (φ : α → β) (w F : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (b : β) (hmass : 0 < ConditionalExpectation.mass φ w b) :
    |ConditionalExpectation.mean φ w F b| ≤
      (∑ a, w a * |F a|) / ConditionalExpectation.mass φ w b := by
  unfold ConditionalExpectation.mean
  rw [abs_div, abs_of_pos hmass]
  exact div_le_div_of_nonneg_right (abs_moment_le_abs_sum φ w F hw b) hmass.le

/-- Residual orthogonality for any measurable test function, without a supplied readout. -/
theorem residual_orthogonal_measurable (φ : α → β) (w F G : α → ℝ)
    (hw : ∀ a, 0 < w a) (hG : ∀ x y, φ x = φ y → G x = G y) :
    (∑ a, w a * (F a - ConditionalExpectation.conditional φ w F a) * G a) = 0 := by
  obtain ⟨g,hg⟩ := ConditionalExpectation.exists_readout φ G hG
  have heq : G = fun a => g (φ a) := funext hg
  rw [heq]
  exact ConditionalExpectation.residual_orthogonal φ w F hw g

end GenericMeanBound

/-- The repaired bound (15), retaining the necessary factor `2^(3|S|)`. -/
theorem approxComponent_conditional_abs_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → Bool) (S T : Finset ι) (z : T → Bool) :
    |ConditionalExpectation.mean (fun x : Cube ι => fun i : T => x i) (weight p)
      (approxComponent p J (fun y => Influence.boolValue (f y)) S) z| ≤
      ((2:ℝ)^(3*S.card) * p^S.card) / weight p z := by
  have hmass : ConditionalExpectation.mass (fun x : Cube ι => fun i : T => x i) (weight p) z =
      weight p z := by
    have hm := ConditionalExpectation.mass_restriction (ι := ι) p (fun i => i ∈ T) z
    rw [Subsingleton.elim (Subtype.fintype (fun i => i ∈ T)) (Finset.Subtype.fintype T)] at hm
    exact hm
  apply (abs_mean_le_div _ _ _ (weight_nonneg hp0.le hp1.le) z
    (by rw [hmass]; exact weight_pos hp0 hp1 z)).trans
  rw [hmass]
  apply div_le_div_of_nonneg_right _ (weight_pos hp0 hp1 z).le
  exact approxComponent_abs_mean_le hp0 hp1 J f S

/-- Fixed-coordinate restriction of a cube point. -/
def restriction (T : Finset ι) (x : Cube ι) : T → Bool := fun i => x i

/-- The generalized Walsh component has zero conditional mean on any set
which omits one of its support coordinates. -/
theorem component_conditional_zero (p : ℝ) (f : Cube ι → ℝ) (S T : Finset ι)
    (hST : ¬ S ⊆ T) (z : T → Bool) :
    ConditionalExpectation.mean (restriction T) (weight p) (Fourier.component p f S) z = 0 := by
  have hlocal : ∀ x y : Cube ι, (∀ i ∈ T, x i = y i) →
      (if restriction T x = z then (1:ℝ) else 0) = (if restriction T y = z then 1 else 0) := by
    intro x y hxy
    have heq : restriction T x = restriction T y := funext (fun i => hxy i i.property)
    rw [heq]
  have horth := component_orthogonal_of_not_subset p f S T hST
    (fun x => if restriction T x = z then 1 else 0) hlocal
  have hm : ConditionalExpectation.moment (restriction T) (weight p) (Fourier.component p f S) z = 0 := by
    rw [ConditionalExpectation.moment_eq_expectation]
    simpa only [mul_ite, mul_one, mul_zero] using horth
  simp only [ConditionalExpectation.mean, hm, zero_div]

omit [Fintype ι] [DecidableEq ι] in
/-- A fixed-coordinate fiber inside a fired local activation is measurable
for the restricted adaptive partition, retaining the actual input labels. -/
theorem fired_fiber_indicator_measurable (J : Activation ι) (S T : Finset ι)
    (hTS : T ⊆ S) (x0 : Cube ι) (hfire : J.fires T x0) (x y : Cube ι)
    (hxy : (restrict J S).SameAtom x y) :
    (if restriction T x = restriction T x0 then (1:ℝ) else 0) =
      (if restriction T y = restriction T x0 then 1 else 0) := by
  have forward (a b : Cube ι) (hab : (restrict J S).SameAtom a b)
      (ha : restriction T a = restriction T x0) : restriction T b = restriction T x0 := by
    have haf : J.fires T a := (J.locality T x0 a (by
      intro i hi
      exact (congrFun ha (⟨i,hi⟩ : T)).symm)).mp hfire
    funext i
    have hai : i.val ∈ (restrict J S).active a :=
      Activation.mem_active_of_fires (show (restrict J S).fires T a from ⟨hTS,haf⟩) i.property
    exact (hab.2 i hai).symm.trans (congrFun ha i)
  have hyx : (restrict J S).SameAtom y x := by
    refine ⟨hxy.1.symm, ?_⟩
    intro i hi
    exact (hxy.2 i (hxy.1 ▸ hi)).symm
  have heq : restriction T x = restriction T x0 ↔ restriction T y = restriction T x0 :=
    ⟨forward x y hxy, forward y x hyx⟩
  simp only [heq]

/-- On a fired proper sub-support, the conditional component has mean zero.
This is Hatami's equation (16), proved via the measurable fiber indicator. -/
theorem approxComponent_conditional_zero_of_fires {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (S T : Finset ι) (hTS : T ⊆ S)
    (hST : ¬ S ⊆ T) (x0 : Cube ι) (hfire : J.fires T x0) :
    ConditionalExpectation.mean (restriction T) (weight p) (approxComponent p J f S)
      (restriction T x0) = 0 := by
  let G := fun x : Cube ι => if restriction T x = restriction T x0 then (1:ℝ) else 0
  have horth := residual_orthogonal_measurable
    (ConditionalExpectation.adaptiveCode (restrict J S)) (weight p)
    (Fourier.component p f S) G (weight_pos hp0 hp1)
    (fun x y hxy => fired_fiber_indicator_measurable J S T hTS x0 hfire x y
      ((ConditionalExpectation.adaptiveCode_eq_iff _ x y).mp hxy))
  have hm : ConditionalExpectation.moment (restriction T) (weight p) (Fourier.component p f S)
      (restriction T x0) =
      ConditionalExpectation.moment (restriction T) (weight p) (approxComponent p J f S)
        (restriction T x0) := by
    apply sub_eq_zero.mp
    rw [ConditionalExpectation.moment_eq_indicator_sum,
      ConditionalExpectation.moment_eq_indicator_sum, ← Finset.sum_sub_distrib]
    convert horth using 1
    apply Finset.sum_congr rfl
    intro x _
    dsimp [G, approxComponent, adaptiveConditional]
    by_cases hx : restriction T x = restriction T x0 <;> simp [hx]
    all_goals ring
  have hmean : ConditionalExpectation.mean (restriction T) (weight p) (Fourier.component p f S)
      (restriction T x0) =
      ConditionalExpectation.mean (restriction T) (weight p) (approxComponent p J f S)
        (restriction T x0) := by
    unfold ConditionalExpectation.mean
    rw [hm]
  rw [← hmean]
  exact component_conditional_zero p f S T hST _

end NarrowDNF.HatamiResidual



