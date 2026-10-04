import NarrowDNF.BourgainSquareFunction
import NarrowDNF.BourgainIntegration
import NarrowDNF.BourgainParameters
import NarrowDNF.BourgainRealCutoff

/-!
# Bourgain's small-component estimate with the paper's threshold

The estimates in this module are fully discharged. No Fourier, square-function,
noise, hypercontractive, or small-component estimate is an assumed hypothesis.
Only the stated bound on the Boolean function's total resampling influence is
an input, as required by Hatami's theorem.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainEstimate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complete integrated Bourgain inequality, using the proven square-function
constants and arbitrary positive auxiliary parameters. -/
theorem smallComponentMass_le_general {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (k M : ℕ) (hM : 0 < M) (η τ C : ℝ)
    (hτ : 0 < τ) (hC0 : 0 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    BourgainComponents.smallComponentMass p (fun x => Influence.boolValue (f x)) k η ≤
      (M : ℝ)^k * η^2 + 2*C*(3 : ℝ)^(2*k)*τ^(2/3 : ℝ) +
        (3 : ℝ)^(2*k)*Real.sqrt C/(Real.sqrt (M : ℝ)*τ) := by
  let F := Finset.univ.filter fun S : Finset ι => S.card ≤ k
  let c := fun x S => Fourier.component p (fun x => Influence.boolValue (f x)) S x
  have h := BourgainIntegration.integrated_bourgain_split
    (ProductMeasure.weight p) (ProductMeasure.weight_nonneg hp0.le hp1.le)
    (ProductMeasure.sum_weight p) F c k M
    (fun S hS => (Finset.mem_filter.mp hS).2) hM η τ hτ
  have hcoord : (∑ i, ∑ x, ProductMeasure.weight p x *
      (BourgainComponents.coordinateSquare F (c x) i)^(2/3 : ℝ)) ≤
        2*C*(3 : ℝ)^(2*k) := by
    have hm := BourgainSquareFunction.sum_coordinateSquare_boolean_moment43 hp0 hp1 f k
    have hC := mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ (3 : ℝ)^(2*k))
    change (∑ i, ProductMeasure.expectation p (fun x =>
      (BourgainComponents.coordinateSquare F (c x) i)^(2/3 : ℝ))) ≤ _
    have hCC : (3 : ℝ)^(2*k)*C ≤ 2*C*(3 : ℝ)^(2*k) := by
      nlinarith [mul_nonneg hC0 (by positivity : 0 ≤ (3 : ℝ)^(2*k))]
    exact hm.trans (hC.trans hCC)
  have hfourth : (∑ x, ProductMeasure.weight p x * (∑ S ∈ F, c x S^2)^2) ≤
      (3 : ℝ)^(4*k) := by
    simpa only [BourgainSquareFunction.squareFunction_eq_finset] using
      BourgainSquareFunction.squareFunction_boolean_fourth hp0 hp1 f k
  have hrootfourth : Real.sqrt (∑ x, ProductMeasure.weight p x * (∑ S ∈ F, c x S^2)^2) ≤
      (3 : ℝ)^(2*k) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [← pow_mul, show 2*k*2 = 4*k by omega]
    exact hfourth
  have hdegree : (∑ x, ProductMeasure.weight p x *
      ∑ i, BourgainComponents.coordinateSquare F (c x) i) ≤ C := by
    have hdeg := BourgainSquareFunction.coordinateSquare_total_mean_le hp0 hp1 f k
    exact hdeg.trans (by linarith)
  have htail : Real.sqrt (∑ x, ProductMeasure.weight p x * (∑ S ∈ F, c x S^2)^2) *
      Real.sqrt (∑ x, ProductMeasure.weight p x *
        ∑ i, BourgainComponents.coordinateSquare F (c x) i) /
          (Real.sqrt (M : ℝ)*τ) ≤
      (3 : ℝ)^(2*k)*Real.sqrt C/(Real.sqrt (M : ℝ)*τ) := by
    apply div_le_div_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) hτ.le)
    exact mul_le_mul hrootfourth (Real.sqrt_le_sqrt hdegree) (Real.sqrt_nonneg _) (by positivity)
  have hmiddle := mul_le_mul_of_nonneg_left hcoord (Real.rpow_nonneg hτ.le (2/3 : ℝ))
  change BourgainComponents.smallComponentMass p (fun x => Influence.boolValue (f x)) k η ≤ _
  exact h.trans (by
    have hh := add_le_add (add_le_add_left hmiddle ((M : ℝ)^k * η^2)) htail
    convert hh using 1; ring)

/-- Complete natural-cutoff small-component estimate with exactly the paper's
Fourier threshold, including the stronger factor-two error margin. -/
theorem smallComponentMass_bound {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) {k : ℕ} (hk : 5 ≤ k) {e C : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hC0 : 0 ≤ C) (hC : C ≤ k)
    (hI : Influence.totalInfluence p f ≤ C) :
    BourgainComponents.smallComponentMass p (fun x => Influence.boolValue (f x)) k
      (BourgainParameters.eta k e) ≤ e^2/(2*(k : ℝ)) := by
  have hM : 0 < BourgainParameters.cutoff k e := by
    have hge : (1 : ℝ) ≤ (BourgainParameters.cutoff k e : ℝ) :=
      (BourgainParameters.realCutoff_ge_one k he he1).trans
        (BourgainParameters.cutoff_lower k e)
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hge)
  have hτ : 0 < BourgainParameters.tau k e := by
    unfold BourgainParameters.tau
    positivity
  exact (smallComponentMass_le_general hp0 hp1 f k
    (BourgainParameters.cutoff k e) hM (BourgainParameters.eta k e)
    (BourgainParameters.tau k e) C hτ hC0 hI).trans
      (BourgainParameters.total_bound hk he he1 hC0 hC)

/-- Hatami's small-component estimate at the actual real cutoff and exact
source epsilon-one. The influence ceiling C is natural, just as in the source.
This is stronger than the epsilon-zero/k version used in Section 4. -/
theorem paper_smallComponentMass_bound {p k e : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (C : ℕ) (hk : 5 ≤ k) (he : 0 < e) (he1 : e ≤ 1)
    (hC : (C : ℝ) ≤ k) (hI : Influence.totalInfluence p f ≤ C) :
    FourierTruncation.smallMassReal p (fun x => Influence.boolValue (f x)) k
      (HatamiParameters.epsilonOne k e) ≤ e^2/k := by
  have hk0 : 0 ≤ k := by linarith
  have hm : 5 ≤ Nat.floor k := (Nat.le_floor_iff hk0).mpr (by norm_num; exact hk)
  have hCm : C ≤ Nat.floor k := (Nat.le_floor_iff hk0).mpr hC
  have hCmr : (C : ℝ) ≤ (Nat.floor k : ℝ) := by exact_mod_cast hCm
  calc
    _ ≤ BourgainComponents.smallComponentMass p (fun x => Influence.boolValue (f x))
        (Nat.floor k) (BourgainParameters.eta (Nat.floor k) e) :=
      BourgainRealCutoff.paper_smallMass_le_natural hp0.le hp1.le hk0 he he1 _
    _ ≤ e^2/(2*(Nat.floor k : ℝ)) :=
      smallComponentMass_bound hp0 hp1 f hm he he1 (Nat.cast_nonneg C) hCmr hI
    _ ≤ e^2/k := BourgainRealCutoff.floor_errorBudget_le (by linarith)

/-- The weaker Section 4 error budget follows from the proved Section 5
small-component estimate and `e ≤ 1`. -/
theorem paper_smallComponentMass_bound_section4 {p k e : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → Bool) (C : ℕ)
    (hk : 5 ≤ k) (he : 0 < e) (he1 : e ≤ 1)
    (hC : (C : ℝ) ≤ k) (hI : Influence.totalInfluence p f ≤ C) :
    FourierTruncation.smallMassReal p (fun x => Influence.boolValue (f x)) k
      (HatamiParameters.epsilonOne k e) ≤ e/k := by
  refine (paper_smallComponentMass_bound hp0 hp1 f C hk he he1 hC hI).trans ?_
  exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1)])
    (by linarith)

end NarrowDNF.BourgainEstimate
