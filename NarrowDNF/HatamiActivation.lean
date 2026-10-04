import NarrowDNF.Fourier
import NarrowDNF.LoadTransport
import NarrowDNF.HatamiParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Hatami's threshold activation family

The local activations and multiplicity-counted load calculation from Appendix A
of arXiv:2609.00240v1. The cutoff is real, as in the source. All threshold masses
are explicit finite sums; no activation-load guarantee is assumed.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiActivation

open ProductMeasure
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability mass of the input restricted to the activation's index set. -/
def localMass (p : ℝ) (T : Finset ι) (x : Cube ι) : ℝ :=
  weight p (fun i : T => x i)

/-- The mass attached to a set is the total retained mass of its supersets. -/
def bMass (retained : Finset (Finset ι)) (m : Finset ι → ℝ) (T : Finset ι) : ℝ :=
  ∑ S ∈ retained, if T ⊆ S then m S else 0

omit [Fintype ι] [DecidableEq ι] in
theorem localMass_congr (p : ℝ) (T : Finset ι) (x y : Cube ι)
    (hxy : ∀ i ∈ T, x i = y i) : localMass p T x = localMass p T y := by
  unfold localMass
  congr 1
  funext i
  exact hxy i i.property

/-- Precisely the threshold activation in Appendix A, including the arity gate. -/
def thresholdActivation (k p δ : ℝ) (retained : Finset (Finset ι))
    (m : Finset ι → ℝ) : Activation ι where
  fires T x := (T.card : ℝ) ≤ k ∧ δ * localMass p T x ≤ bMass retained m T
  locality T x y hxy := by rw [localMass_congr p T x y hxy]

omit [Fintype ι] in
theorem bMass_nonneg (retained : Finset (Finset ι)) (m : Finset ι → ℝ)
    (hm : ∀ S ∈ retained, 0 ≤ m S) (T : Finset ι) : 0 ≤ bMass retained m T := by
  apply Finset.sum_nonneg
  intro S hS
  split_ifs <;> simp_all

theorem bitWeight_antitone {p : ℝ} (hp : p ≤ 1/2) : Antitone (bitWeight p) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [bitWeight, Bool.le_iff_imp]; linarith

omit [Fintype ι] [DecidableEq ι] in
theorem localMass_antitone {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (T : Finset ι) : Antitone (localMass p T) := by
  intro x y hxy
  apply Finset.prod_le_prod
  · intro i _
    exact bitWeight_nonneg hp0 (by linarith) _
  · intro i _
    exact bitWeight_antitone hp (hxy i)

omit [Fintype ι] in
theorem thresholdActivation_increasing {k p δ : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hδ : 0 ≤ δ)
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ) :
    (thresholdActivation k p δ retained m).Increasing := by
  intro T x y hxy hx
  exact ⟨hx.1, (mul_le_mul_of_nonneg_left (localMass_antitone hp0 hp T hxy) hδ).trans hx.2⟩

omit [Fintype ι] in
theorem thresholdActivation_arity {k p δ : ℝ} (d : ℕ) (hkd : k ≤ (d : ℝ))
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ) :
    (thresholdActivation k p δ retained m).ArityLE d := by
  intro T hT x hx
  have hc : (d : ℝ) < T.card := by exact_mod_cast hT
  exact (not_le_of_gt hc) (hx.1.trans hkd)

omit [Fintype ι] in
theorem thresholdActivation_arity_ceil (k p δ : ℝ)
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ) :
    (thresholdActivation k p δ retained m).ArityLE (Nat.ceil k) :=
  thresholdActivation_arity _ (Nat.le_ceil k) retained m

omit [Fintype ι] in
@[simp] theorem localMass_extendLocal (p : ℝ) (T : Finset ι) (z : T → Bool) :
    localMass p T (Activation.extendLocal T z) = weight p z := by
  unfold localMass
  congr 1
  funext i
  simp [Activation.extendLocal, i.property]

/-- Thresholding the marginal point mass bounds each activation probability. -/
theorem threshold_probability_le {k p δ : ℝ} (hδ : 0 < δ)
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ)
    (hm : ∀ S ∈ retained, 0 ≤ m S) (T : Finset ι) :
    probability p ((thresholdActivation k p δ retained m).fires T) ≤
      (2 : ℝ)^T.card * bMass retained m T / δ := by
  rw [Activation.probability_restrict]
  unfold probability expectation
  calc
    _ ≤ ∑ z : T → Bool, bMass retained m T / δ := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : (thresholdActivation k p δ retained m).fires T (Activation.extendLocal T z)
      · simp only [if_pos hz, mul_one]
        apply (le_div_iff₀ hδ).mpr
        simpa only [localMass_extendLocal, mul_comm] using hz.2
      · simp only [if_neg hz, mul_zero]
        exact div_nonneg (bMass_nonneg retained m hm T) hδ.le
    _ = _ := by simp; ring

omit [Fintype ι] [DecidableEq ι] in
/-- Summing `2^|T|` over subsets gives `3^|S|`, rather than an ambient-dimension factor. -/
theorem sum_powerset_two_pow (S : Finset ι) :
    (∑ T ∈ S.powerset, (2 : ℝ)^T.card) = (3 : ℝ)^S.card := by
  have h := (Finset.prod_add_one (f := fun _ : ι => (2 : ℝ)) S).symm
  norm_num at h
  exact h

theorem sum_subsets_eq (S : Finset ι) (F : Finset ι → ℝ) :
    (∑ T : Finset ι, if T ⊆ S then F T else 0) = ∑ T ∈ S.powerset, F T := by
  have hs : (Finset.univ.filter fun T : Finset ι => T ⊆ S) = S.powerset := by
    ext T
    simp
  rw [← Finset.sum_filter, hs]

omit [Fintype ι] [DecidableEq ι] in
theorem powerset_multiplicity_le {k : ℝ} (hk0 : 0 ≤ k) (S : Finset ι)
    (hS : (S.card : ℝ) ≤ k) :
    (∑ T ∈ S.powerset, (T.card : ℝ) * (2 : ℝ)^T.card) ≤ k * (2 : ℝ)^(2*k) := by
  have hpow : (3 : ℝ)^S.card ≤ (2 : ℝ)^(2*k) := by
    calc
      (3 : ℝ)^S.card ≤ (4 : ℝ)^S.card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (2 : ℝ)^(2 * (S.card : ℝ)) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
        norm_num
      _ ≤ (2 : ℝ)^(2*k) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    _ ≤ ∑ T ∈ S.powerset, k * (2 : ℝ)^T.card := by
      apply Finset.sum_le_sum
      intro T hT
      have hc : (T.card : ℝ) ≤ S.card := by
        exact_mod_cast Finset.card_le_card (Finset.mem_powerset.mp hT)
      exact mul_le_mul_of_nonneg_right (hc.trans hS) (by positivity)
    _ = k * (3 : ℝ)^S.card := by rw [← Finset.mul_sum, sum_powerset_two_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hk0

/-- Multiplicity-counted activation load, reduced to the retained input masses. -/
theorem threshold_load_le {k p δ : ℝ} (hk0 : 0 ≤ k) (hδ : 0 < δ)
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ)
    (hm : ∀ S ∈ retained, 0 ≤ m S)
    (hcard : ∀ S ∈ retained, (S.card : ℝ) ≤ k) :
    (thresholdActivation k p δ retained m).load p ≤
      (k * (2 : ℝ)^(2*k) / δ) * ∑ S ∈ retained, m S := by
  unfold Activation.load
  calc
    _ ≤ ∑ T : Finset ι, (T.card : ℝ) *
        ((2 : ℝ)^T.card * bMass retained m T / δ) := by
      apply Finset.sum_le_sum
      intro T _
      exact mul_le_mul_of_nonneg_left (threshold_probability_le hδ retained m hm T)
        (Nat.cast_nonneg _)
    _ = ∑ T : Finset ι, ∑ S ∈ retained,
        if T ⊆ S then ((T.card : ℝ) * (2 : ℝ)^T.card) * (m S / δ) else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      simp only [bMass, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> simp_all; ring
    _ = ∑ S ∈ retained, ∑ T : Finset ι,
        if T ⊆ S then ((T.card : ℝ) * (2 : ℝ)^T.card) * (m S / δ) else 0 :=
      Finset.sum_comm
    _ = ∑ S ∈ retained,
        (∑ T ∈ S.powerset, (T.card : ℝ) * (2 : ℝ)^T.card) * (m S / δ) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [sum_subsets_eq, Finset.sum_mul]
    _ ≤ ∑ S ∈ retained, (k * (2 : ℝ)^(2*k)) * (m S / δ) := by
      apply Finset.sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_right (powerset_multiplicity_le hk0 S (hcard S hS))
        (div_nonneg (hm S hS) hδ.le)
    _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_div]; ring

omit [Fintype ι] in
/-- Full support makes the expected reciprocal marginal mass exactly the
number of local Boolean inputs. -/
theorem reciprocal_mass_expectation {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (T : Finset ι) :
    expectation p (fun z : T → Bool => 1 / weight p z) = (2 : ℝ)^T.card := by
  unfold expectation
  have hpoint (z : T → Bool) : weight p z * (1 / weight p z) = 1 := by
    exact mul_one_div_cancel (ne_of_gt (weight_pos hp0 hp1 z))
  simp_rw [hpoint]
  simp

omit [Fintype ι] in
/-- Exact pointwise inequality used in the source's load calculation. -/
theorem threshold_indicator_le {k p δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hδ : 0 < δ) (retained : Finset (Finset ι)) (m : Finset ι → ℝ)
    (hm : ∀ S ∈ retained, 0 ≤ m S) (T : Finset ι) (x : Cube ι) :
    (if (thresholdActivation k p δ retained m).fires T x then (1 : ℝ) else 0) ≤
      bMass retained m T / (δ * localMass p T x) := by
  have hmass : 0 < localMass p T x := weight_pos hp0 hp1 _
  by_cases h : (thresholdActivation k p δ retained m).fires T x
  · simp only [if_pos h]
    exact (le_div_iff₀ (mul_pos hδ hmass)).mpr (by simpa using h.2)
  · simp only [if_neg h]
    exact div_nonneg (bMass_nonneg retained m hm T) (mul_pos hδ hmass).le

/-- The retained Fourier family, using the finite-cube characterization
of `‖F_S‖∞ > η` as the existence of an input with magnitude greater than `η`. -/
def significantSets (p : ℝ) (f : Cube ι → ℝ) (k η : ℝ) : Finset (Finset ι) :=
  Finset.univ.filter fun S => (S.card : ℝ) ≤ k ∧ ∃ x, η < |Fourier.component p f S x|

/-- The exact event probability appearing in the source's definition of `b_T`. -/
def componentTailMass (p : ℝ) (f : Cube ι → ℝ) (η : ℝ) (S : Finset ι) : ℝ :=
  probability p (fun x => η ≤ |Fourier.component p f S x|)

/-- Locality identifies the global encoding of each tail probability with
the coordinate marginal used in the source. -/
theorem componentTailMass_local (p : ℝ) (f : Cube ι → ℝ) (η : ℝ) (S : Finset ι) :
    componentTailMass p f η S = probability p (fun z : S → Bool =>
      η ≤ |Fourier.component p f S (Activation.extendLocal S z)|) := by
  unfold componentTailMass probability
  have h := expectation_local p (fun i => i ∈ S)
    (fun x => if η ≤ |Fourier.component p f S x| then (1 : ℝ) else 0) (by
      intro x y hxy
      dsimp only
      rw [Fourier.component_locality p f S x y hxy])
  convert h using 1
  congr 1
  exact Subsingleton.elim _ _

/-- The source's threshold activations, specialized to its actual Fourier masses. -/
def fourierActivation (k p δ η : ℝ) (f : Cube ι → ℝ) : Activation ι :=
  thresholdActivation k p δ (significantSets p f k η) (componentTailMass p f η)

theorem significantSets_card (p : ℝ) (f : Cube ι → ℝ) (k η : ℝ)
    (S : Finset ι) (hS : S ∈ significantSets p f k η) : (S.card : ℝ) ≤ k :=
  (Finset.mem_filter.mp hS).2.1

theorem componentTailMass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Cube ι → ℝ) (η : ℝ) (S : Finset ι) : 0 ≤ componentTailMass p f η S :=
  probability_nonneg hp0 hp1 _

/-- A realized local tail event contributes at least its marginal point mass. -/
theorem localMass_le_componentTailMass {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Cube ι → ℝ) (η : ℝ) (S : Finset ι) (x : Cube ι)
    (hx : η ≤ |Fourier.component p f S x|) :
    localMass p S x ≤ componentTailMass p f η S := by
  rw [componentTailMass_local]
  let z : S → Bool := fun i => x i
  have hcomp : Fourier.component p f S (Activation.extendLocal S z) =
      Fourier.component p f S x := by
    apply Fourier.component_locality
    intro i hi
    simp [Activation.extendLocal, hi, z]
  have hz : η ≤ |Fourier.component p f S (Activation.extendLocal S z)| := by
    simpa only [hcomp] using hx
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (S → Bool)))
    (f := fun y => weight p y *
      (if η ≤ |Fourier.component p f S (Activation.extendLocal S y)| then (1 : ℝ) else 0))
    (by intro y _; apply mul_nonneg (weight_nonneg hp0 hp1 y); split_ifs <;> norm_num)
    (Finset.mem_univ z)
  simpa only [if_pos hz, mul_one] using hsingle

omit [Fintype ι] [DecidableEq ι] in
/-- Every local input has mass at least `p^|S|` in the low-bias range. -/
theorem pow_le_localMass {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (S : Finset ι) (x : Cube ι) : p^S.card ≤ localMass p S x := by
  calc
    _ = ∏ i : S, p := by simp
    _ ≤ ∏ i : S, bitWeight p (x i) := by
      apply Finset.prod_le_prod
      · intro _ _
        exact hp0
      · intro i _
        cases x i <;> simp [bitWeight]; linarith

/-- A significant component has a tail event with mass at least `p^|S|`. -/
theorem pow_le_componentTailMass_of_significant {k p η : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (f : Cube ι → ℝ) (S : Finset ι)
    (hS : S ∈ significantSets p f k η) : p^S.card ≤ componentTailMass p f η S := by
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hS).2.2
  exact (pow_le_localMass hp0 hp S x).trans
    (localMass_le_componentTailMass hp0 (by linarith) f η S x hx.le)

omit [Fintype ι] in
theorem mass_le_bMass (retained : Finset (Finset ι)) (m : Finset ι → ℝ)
    (hm : ∀ S ∈ retained, 0 ≤ m S) (S : Finset ι) (hS : S ∈ retained) :
    m S ≤ bMass retained m S := by
  have h := Finset.single_le_sum (s := retained)
    (f := fun T => if S ⊆ T then m T else 0)
    (by intro T hT; dsimp only; split_ifs <;> simp_all) hS
  simpa only [ite_true, Finset.Subset.refl] using h

/-- A retained component above the threshold activates its entire support.
This supplies the source-specific coverage used in the residual argument. -/
theorem fourierActivation_fires_of_component_large {k p δ η : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ)
    (S : Finset ι) (x : Cube ι) (hS : S ∈ significantSets p f k η)
    (hx : η ≤ |Fourier.component p f S x|) :
    (fourierActivation k p δ η f).fires S x := by
  refine ⟨significantSets_card p f k η S hS, ?_⟩
  calc
    δ * localMass p S x ≤ localMass p S x := by
      simpa using mul_le_mul_of_nonneg_right hδ (weight_nonneg hp0 hp1 (fun i : S => x i))
    _ ≤ componentTailMass p f η S := localMass_le_componentTailMass hp0 hp1 f η S x hx
    _ ≤ bMass (significantSets p f k η) (componentTailMass p f η) S :=
      mass_le_bMass _ _ (fun T _ => componentTailMass_nonneg hp0 hp1 f η T) S hS

theorem component_lt_of_not_fires {k p δ η : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ)
    (S : Finset ι) (x : Cube ι) (hS : S ∈ significantSets p f k η)
    (hx : ¬ (fourierActivation k p δ η f).fires S x) :
    |Fourier.component p f S x| < η := by
  by_contra h
  exact hx (fourierActivation_fires_of_component_large hp0 hp1 hδ f S x hS (le_of_not_gt h))

/-- Squared Markov bound for the actual absolute-value tail event. -/
theorem probability_abs_ge_le_sq {p η : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hη : 0 < η) (F : Cube ι → ℝ) :
    probability p (fun x => η ≤ |F x|) ≤ expectation p (fun x => (F x)^2) / η^2 := by
  have h : η^2 * probability p (fun x => η ≤ |F x|) ≤
      expectation p (fun x => (F x)^2) := by
    rw [probability, ← expectation_const_mul]
    apply expectation_mono hp0 hp1
    intro x
    by_cases hx : η ≤ |F x|
    · simp only [if_pos hx, mul_one]
      nlinarith [sq_abs (F x)]
    · simp only [if_neg hx, mul_zero]
      exact sq_nonneg _
  apply (le_div_iff₀ (sq_pos_of_pos hη)).mpr
  linarith

theorem componentTailMass_le {p η : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hη : 0 < η) (f : Cube ι → ℝ) (S : Finset ι) :
    componentTailMass p f η S ≤ Fourier.setCoefficient p f S ^ 2 / η^2 := by
  have h := probability_abs_ge_le_sq hp0.le hp1.le hη (Fourier.component p f S)
  rw [Fourier.component_sq_mean hp0 hp1] at h
  exact h

/-- Parseval and Markov give the retained tail-mass bound, without an
assumption about the number or distribution of retained subsets. -/
theorem sum_componentTailMass_le {p η : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hη : 0 < η) (f : Cube ι → Bool) (retained : Finset (Finset ι)) :
    (∑ S ∈ retained, componentTailMass p (fun x => Influence.boolValue (f x)) η S) ≤
      1 / η^2 := by
  calc
    _ ≤ ∑ S ∈ retained, Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 / η^2 := by
      apply Finset.sum_le_sum
      intro S _
      exact componentTailMass_le hp0 hp1 hη _ S
    _ = (∑ S ∈ retained, Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2) / η^2 :=
      (Finset.sum_div _ _ _).symm
    _ ≤ 1 / η^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg η)
      apply le_trans _ (Fourier.boolean_energy_le_one hp0 hp1 f)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ retained)
      intro S _ _
      exact sq_nonneg _

theorem fourierActivation_increasing {k p δ η : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hδ : 0 ≤ δ) (f : Cube ι → ℝ) :
    (fourierActivation k p δ η f).Increasing :=
  thresholdActivation_increasing hp0 hp hδ _ _

theorem fourierActivation_arity (k p δ η : ℝ) (f : Cube ι → ℝ) :
    (fourierActivation k p δ η f).ArityLE (Nat.ceil k) :=
  thresholdActivation_arity_ceil k p δ _ _

/-- The complete Fourier-specialized multiplicity load estimate of Appendix A. -/
theorem fourierActivation_load_le {k p δ η : ℝ} (hk0 : 0 ≤ k)
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : 0 < δ) (hη : 0 < η)
    (f : Cube ι → Bool) :
    (fourierActivation k p δ η (fun x => Influence.boolValue (f x))).load p ≤
      k * (2 : ℝ)^(2*k) / (δ * η^2) := by
  apply le_trans (threshold_load_le hk0 hδ _ _
    (fun S _ => componentTailMass_nonneg hp0.le hp1.le _ η S)
    (fun S hS => significantSets_card p _ k η S hS))
  calc
    _ ≤ (k * (2 : ℝ)^(2*k) / δ) * (1 / η^2) :=
      mul_le_mul_of_nonneg_left (sum_componentTailMass_le hp0 hp1 hη f _)
        (by positivity)
    _ = _ := by ring

/-- Appendix A's activation family at its exact parameter values. -/
def paperActivation (a C p : ℝ) (f : Cube ι → Bool) : Activation ι :=
  fourierActivation (1000*C/a) p
    (HatamiParameters.delta (1000*C/a))
    (HatamiParameters.epsilonOne (1000*C/a) (a/1000))
    (fun x => Influence.boolValue (f x))

/-- The explicit family is local by construction, increasing in the low-bias
range, has the stated arity, and satisfies the exact final exponential load. -/
theorem paperActivation_properties {a C p : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : 1 ≤ C) (hp0 : 0 < p) (hp : p ≤ 1/2) (f : Cube ι → Bool) :
    (paperActivation a C p f).Increasing ∧
      (paperActivation a C p f).ArityLE (Nat.ceil (1000*C/a)) ∧
      (paperActivation a C p f).load p ≤ Real.exp (10000000000*C^2/a^2) := by
  have hk0 : 0 ≤ 1000*C/a := by positivity
  have hδ := HatamiParameters.delta_pos (1000*C/a)
  have hη := HatamiParameters.epsilonOne_pos (by positivity : 0 < a/1000) (1000*C/a)
  refine ⟨fourierActivation_increasing hp0.le hp hδ.le _,
    fourierActivation_arity _ _ _ _ _, ?_⟩
  exact (fourierActivation_load_le hk0 hp0 (by linarith) hδ hη f).trans
    (HatamiParameters.paper_load_bound ha ha1 hC)

/-- The paper's `C_f`, explicitly derived from resampling influence. -/
def ceilInfluence (p : ℝ) (f : Cube ι → Bool) : ℕ := Nat.ceil (Influence.totalInfluence p f)

def paperActivationOfInfluence (a p : ℝ) (f : Cube ι → Bool) : Activation ι :=
  paperActivation a (ceilInfluence p f : ℝ) p f

/-- Positive influence supplies `C_f ≥ 1`; no independent complexity or
activation-load hypothesis is needed for the construction and these bounds. -/
theorem paperActivationOfInfluence_properties {a p : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hp0 : 0 < p) (hp : p ≤ 1/2) (f : Cube ι → Bool)
    (hI : 0 < Influence.totalInfluence p f) :
    (paperActivationOfInfluence a p f).Increasing ∧
      (paperActivationOfInfluence a p f).ArityLE
        (Nat.ceil (1000*(ceilInfluence p f : ℝ)/a)) ∧
      (paperActivationOfInfluence a p f).load p ≤
        Real.exp (10000000000*(ceilInfluence p f : ℝ)^2/a^2) := by
  have hCN : 1 ≤ ceilInfluence p f := Nat.ceil_pos.mpr hI
  have hC : (1 : ℝ) ≤ (ceilInfluence p f : ℝ) := by exact_mod_cast hCN
  exact paperActivation_properties ha ha1 hC hp0 hp f

end NarrowDNF.HatamiActivation
