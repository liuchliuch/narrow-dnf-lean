import NarrowDNF.BourgainEstimate
import NarrowDNF.HatamiResidual
import NarrowDNF.HatamiCrossTerms
import NarrowDNF.MainStatements

/-!
# Hatami's quantitative activation input

Assembly of the actual Fourier truncation, the reconstructed Bourgain estimate,
the repaired adaptive residual proof, and threshold decoding for Lemma 2.1.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.HatamiInput
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nonnegativity of the actual total resampling influence. -/
theorem totalInfluence_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → Bool) : 0 ≤ Influence.totalInfluence p f := by
  rw [Fourier.totalInfluence_spectral_finset hp0 hp1]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun S _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- Real-cutoff high-frequency bound with the exact factor two from
resampling influence. -/
theorem highDegreeReal_mass_le {p k : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hk : 0 < k) (f : Cube ι → Bool) :
    (∑ S : Finset ι, if k < (S.card : ℝ) then
      Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 else 0) ≤
        Influence.totalInfluence p f / (2*k) := by
  classical
  have hweighted : k * (∑ S : Finset ι, if k < (S.card : ℝ) then
      Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 else 0) ≤
      ∑ S : Finset ι, (S.card : ℝ) *
        Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S _
    split_ifs with hS
    · exact mul_le_mul_of_nonneg_right hS.le (sq_nonneg _)
    · simpa only [mul_zero] using mul_nonneg (Nat.cast_nonneg S.card)
        (sq_nonneg (Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S))
  apply (le_div_iff₀ (by positivity : 0 < 2*k)).mpr
  rw [Fourier.totalInfluence_spectral_finset hp0 hp1]
  nlinarith

/-- The paper's exact parameter multiplication identity. -/
theorem paper_parameter_product {a : ℝ} (ha : 0 < a) (C : ℝ) :
    (1000*C/a)*(a/1000) = C := by
  field_simp

/-- In the nonconstant case the paper's cutoff is at least 1000. -/
theorem paper_cutoff_ge {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hC : 1 ≤ C) :
    (1000 : ℝ) ≤ 1000*C/a := by
  apply (le_div_iff₀ ha).mpr
  linarith

/-- The two pruning steps have squared error at most two epsilon-zero for
exactly the retained family appearing in the source activation construction. -/
theorem paper_truncation_error_le {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (f : Cube ι → Bool) (C : ℕ)
    (hC : 1 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    ConditionalExpectation.squaredError (ProductMeasure.weight p)
      (fun x => Influence.boolValue (f x))
      (HatamiResidual.truncated p (fun x => Influence.boolValue (f x))
        (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x))
          (1000*(C : ℝ)/a) (HatamiParameters.epsilonOne (1000*(C : ℝ)/a) (a/1000)))) ≤
            2*(a/1000) := by
  let k := 1000*(C : ℝ)/a
  let e := a/1000
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hk1000 : 1000 ≤ k := paper_cutoff_ge ha ha1 hCr
  have hk0 : 0 < k := by linarith
  have he0 : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by dsimp [e]; linarith
  have hke : k*e = C := paper_parameter_product ha (C : ℝ)
  have hCk : (C : ℝ) ≤ k := by nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr he1)]
  have htrunc := FourierTruncation.significant_remainder_le hp0 hp1
    (fun x => Influence.boolValue (f x)) k (HatamiParameters.epsilonOne k e)
  have hhigh := highDegreeReal_mass_le hp0 hp1 hk0 f
  have hhigh' : Influence.totalInfluence p f/(2*k) ≤ e := by
    apply (div_le_iff₀ (by positivity : 0 < 2*k)).mpr
    nlinarith
  have hsmall := BourgainEstimate.paper_smallComponentMass_bound_section4
    hp0 hp1 f C (by linarith) he0 he1 hCk hI
  have hsmall' : e/k ≤ e := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith
  change ConditionalExpectation.squaredError (ProductMeasure.weight p)
      (fun x => Influence.boolValue (f x))
      (FourierTruncation.partialSum p (fun x => Influence.boolValue (f x))
        (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x))
          k (HatamiParameters.epsilonOne k e))) ≤ 2*e
  linarith

/-- The empty activation family used for the zero-influence case. -/
def emptyActivation : Activation ι where
  fires _ _ := False
  locality _ _ _ _ := Iff.rfl

/-- Empty activations have zero load and satisfy every arity cap. -/
theorem emptyActivation_properties (p : ℝ) (d : ℕ) :
    (emptyActivation : Activation ι).Increasing ∧
      (emptyActivation : Activation ι).ArityLE d ∧
      (emptyActivation : Activation ι).load p = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro S x y hxy hx
    exact False.elim hx
  · intro S hS x hx
    exact hx
  · simp [Activation.load, emptyActivation, ProductMeasure.probability]

/-- Zero total influence is handled without dividing by its ceiling. -/
theorem zero_influence_input {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (f : Cube ι → Bool) (hI : Influence.totalInfluence p f = 0)
    (d : ℕ) :
    ∃ (J : Activation ι) (h : Cube ι → Bool), J.Increasing ∧
      ProductMeasure.error p f h ≤ a ∧ J.Measurable h ∧ J.ArityLE d ∧ J.load p ≤ 1 := by
  refine ⟨emptyActivation, f, (emptyActivation_properties p d).1, ?_, ?_,
    (emptyActivation_properties p d).2.1, ?_⟩
  · simpa only [ProductMeasure.error_self] using ha.le
  · intro x y _
    exact Fourier.constant_of_totalInfluence_zero hp0 hp1 f hI x y
  · rw [(emptyActivation_properties p d).2.2]
    norm_num

/-- The exact source delta is at most one for every real cutoff. -/
theorem paper_delta_le_one (k : ℝ) : HatamiParameters.delta k ≤ 1 := by
  unfold HatamiParameters.delta
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith [sq_nonneg k])

/-- The reciprocal epsilon-zero hypothesis in the repaired cross-term estimate
follows from the source ceiling C being at least one. -/
theorem paper_reciprocal_le_cutoff {a C : ℝ} (ha : 0 < a) (hC : 1 ≤ C) :
    (a/1000)⁻¹ ≤ 1000*C/a := by
  rw [inv_div]
  exact div_le_div_of_nonneg_right (by linarith) ha.le

/-- The direct source-parameter instance of the fully proved Bourgain bound. -/
theorem paper_smallMass_bound {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (f : Cube ι → Bool) (C : ℕ)
    (hC : 1 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    FourierTruncation.smallMassReal p (fun x => Influence.boolValue (f x))
      (1000*(C : ℝ)/a) (HatamiParameters.epsilonOne (1000*(C : ℝ)/a) (a/1000)) ≤
        (a/1000)^2/(1000*(C : ℝ)/a) := by
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hk := paper_cutoff_ge ha ha1 hCr
  apply BourgainEstimate.paper_smallComponentMass_bound hp0 hp1 f C
    (by linarith) (by positivity) (by linarith)
  · apply (le_div_iff₀ ha).mpr
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    nlinarith [mul_nonneg hC0 (sub_nonneg.mpr ha1)]
  · exact hI

/-- The actual restricted-component approximation obeys the source Step III
error budget after inserting the proved small-mass and repaired cross bounds. -/
theorem paper_approxTruncated_error_le {p a : ℝ} (hp0 : 0 < p) (hp : p ≤ 1/2)
    (ha : 0 < a) (ha1 : a ≤ 1) (f : Cube ι → Bool) (C : ℕ)
    (hC : 1 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    ConditionalExpectation.squaredError (ProductMeasure.weight p)
      (HatamiResidual.truncated p (fun x => Influence.boolValue (f x))
        (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x))
          (1000*(C : ℝ)/a) (HatamiParameters.epsilonOne (1000*(C : ℝ)/a) (a/1000))))
      (HatamiResidual.approxTruncated p (HatamiActivation.paperActivation a C p f)
        (fun x => Influence.boolValue (f x))
        (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x))
          (1000*(C : ℝ)/a) (HatamiParameters.epsilonOne (1000*(C : ℝ)/a) (a/1000)))) ≤
            3*(a/1000) := by
  let k := 1000*(C : ℝ)/a
  let e := a/1000
  have hp1 : p < 1 := by linarith
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hk1000 : 1000 ≤ k := paper_cutoff_ge ha ha1 hCr
  have hk0 : 0 < k := by linarith
  have he0 : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by dsimp [e]; linarith
  have hd := HatamiParameters.delta_pos k
  have hη := HatamiParameters.epsilonOne_pos he0 k
  have h := HatamiCrossTerms.approxTruncated_residual_le
    (k := k) hp0 hp (by linarith) hd.le (paper_delta_le_one k) hη f
  have hsmall := paper_smallMass_bound hp0 hp1 ha ha1 f C hC hI
  have hmul := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 2*k)
  have hcancel : 2*k*(e^2/k) = 2*e^2 := by field_simp
  change 2*k*FourierTruncation.smallMassReal p (fun x => Influence.boolValue (f x))
    k (HatamiParameters.epsilonOne k e) ≤ 2*k*(e^2/k) at hmul
  rw [hcancel] at hmul
  have hcross := HatamiParameters.corrected_cross_bound he0 (by linarith : 1 ≤ k)
    (paper_reciprocal_le_cutoff ha hCr)
  change (2 : ℝ)^(9*k)*HatamiParameters.delta k/(HatamiParameters.epsilonOne k e)^2 ≤ e at hcross
  change ConditionalExpectation.squaredError (ProductMeasure.weight p)
    (HatamiResidual.truncated p (fun x => Influence.boolValue (f x))
      (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x)) k
        (HatamiParameters.epsilonOne k e)))
    (HatamiResidual.approxTruncated p
      (HatamiActivation.fourierActivation k p (HatamiParameters.delta k)
        (HatamiParameters.epsilonOne k e) (fun x => Influence.boolValue (f x)))
      (fun x => Influence.boolValue (f x))
      (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x)) k
        (HatamiParameters.epsilonOne k e))) ≤ 3*e
  nlinarith [mul_nonneg he0.le (sub_nonneg.mpr he1)]

/-- The complete conditional-variance estimate for exactly the paper's
activation family. All Fourier and adaptive estimates have been discharged. -/
theorem paper_conditional_variance_le {p a : ℝ} (hp0 : 0 < p) (hp : p ≤ 1/2)
    (ha : 0 < a) (ha1 : a ≤ 1) (f : Cube ι → Bool) (C : ℕ)
    (hC : 1 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    ConditionalExpectation.squaredError (ProductMeasure.weight p)
      (fun x => Influence.boolValue (f x))
      (HatamiResidual.adaptiveConditional p (HatamiActivation.paperActivation a C p f)
        (fun x => Influence.boolValue (f x))) ≤ 10*(a/1000) := by
  apply HatamiResidual.final_residual_le_ten hp0 (by linarith)
    (HatamiActivation.paperActivation a C p f) (fun x => Influence.boolValue (f x))
    (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x))
      (1000*(C : ℝ)/a) (HatamiParameters.epsilonOne (1000*(C : ℝ)/a) (a/1000)))
    (a/1000)
  · exact paper_truncation_error_le hp0 (by linarith) ha ha1 f C hC hI
  · exact paper_approxTruncated_error_le hp0 hp ha ha1 f C hC hI

/-- The actual threshold decoder for the exact source activation family has
error at most the requested a. -/
theorem paper_decoder_error_le {p a : ℝ} (hp0 : 0 < p) (hp : p ≤ 1/2)
    (ha : 0 < a) (ha1 : a ≤ 1) (f : Cube ι → Bool) (C : ℕ)
    (hC : 1 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    ProductMeasure.error p f
      (ConditionalExpectation.adaptiveDecoder p (HatamiActivation.paperActivation a C p f) f) ≤ a := by
  have hvariance := paper_conditional_variance_le hp0 hp ha ha1 f C hC hI
  have hround := ConditionalExpectation.adaptiveDecoder_error_le_four hp0.le (by linarith)
    (HatamiActivation.paperActivation a C p f) f
  change ProductMeasure.error p f
    (ConditionalExpectation.adaptiveDecoder p (HatamiActivation.paperActivation a C p f) f) ≤
      4 * ConditionalExpectation.squaredError (ProductMeasure.weight p)
        (fun x => Influence.boolValue (f x))
        (HatamiResidual.adaptiveConditional p (HatamiActivation.paperActivation a C p f)
          (fun x => Influence.boolValue (f x))) at hround
  linarith

/-- Lemma 2.1 of the target paper, with its exact simultaneous approximation,
increasing activation, arity and multiplicity-counted load conclusions. -/
theorem hatami_arity_load : NarrowDNF.HatamiArityLoad := by
  classical
  intro n p hp0 hp f a ha ha1
  dsimp only
  have hp1 : p < 1 := by linarith
  by_cases hI0 : Influence.totalInfluence p f = 0
  · obtain ⟨J,h,hJ,he,hm,hd,hL⟩ := zero_influence_input hp0 hp1 ha f hI0
      (Nat.ceil (1000*(Nat.ceil (Influence.totalInfluence p f) : ℝ)/a))
    refine ⟨J,h,hJ,he,hm,hd,hL.trans ?_⟩
    exact Real.one_le_exp_iff.mpr (by positivity)
  · have hIpos : 0 < Influence.totalInfluence p f :=
      lt_of_le_of_ne (totalInfluence_nonneg hp0 hp1 f) (Ne.symm hI0)
    let C := Nat.ceil (Influence.totalInfluence p f)
    have hC : 1 ≤ C := Nat.ceil_pos.mpr hIpos
    have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
    have hI : Influence.totalInfluence p f ≤ C := Nat.le_ceil _
    let J := HatamiActivation.paperActivation a C p f
    have hprops := HatamiActivation.paperActivation_properties ha ha1 hCr hp0 hp f
    refine ⟨J, ConditionalExpectation.adaptiveDecoder p J f, hprops.1, ?_,
      ConditionalExpectation.adaptiveDecoder_measurable p J f, hprops.2.1, hprops.2.2⟩
    exact paper_decoder_error_le hp0 hp ha ha1 f C hC hI

end NarrowDNF.HatamiInput
