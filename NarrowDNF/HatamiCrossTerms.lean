import NarrowDNF.HatamiResidual
import NarrowDNF.ConditionalIndependence
import NarrowDNF.RankGrouping
import NarrowDNF.FourierTruncation
import NarrowDNF.ResidualGram

/-!
# Hatami's corrected cross-term estimate

Finite cross-term estimates for the exact restricted-activation conditional
components. The repaired coefficient factor is retained explicitly.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiCrossTerms

open ProductMeasure HatamiResidual HatamiActivation
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inactive overlap-fiber kernel used in Hatami's cross-term sum. -/
def inactiveKernel (p : ℝ) (J : Activation ι) (T : Finset ι) : ℝ :=
  expectation p (fun x => if J.fires T x then 0 else 1 / localMass p T x ^ 2)

theorem inactiveKernel_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Activation ι) (T : Finset ι) : 0 ≤ inactiveKernel p J T := by
  apply expectation_nonneg hp0 hp1
  intro x
  split_ifs <;> positivity

/-- Distinct supports have a proper intersection in at least one component;
a fired intersection therefore kills their product of conditional means. -/
theorem conditional_product_zero_of_fires {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (S R : Finset ι) (hSR : S ≠ R)
    (x : Cube ι) (hx : J.fires (S ∩ R) x) :
    ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J f S)
      (restriction (S ∩ R) x) *
    ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J f R)
      (restriction (S ∩ R) x) = 0 := by
  by_cases hS : S ⊆ S ∩ R
  · have hR : ¬ R ⊆ S ∩ R := by
      intro hR
      apply hSR
      exact Finset.Subset.antisymm (hS.trans Finset.inter_subset_right)
        (hR.trans Finset.inter_subset_left)
    rw [approxComponent_conditional_zero_of_fires hp0 hp1 J f R (S ∩ R)
      Finset.inter_subset_right hR x hx, mul_zero]
  · rw [approxComponent_conditional_zero_of_fires hp0 hp1 J f S (S ∩ R)
      Finset.inter_subset_left hS x hx, zero_mul]

/-- Exact pairwise cross bound before bounding the degrees by a common cutoff. -/
theorem pair_cross_le_kernel {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → Bool) (S R : Finset ι) (hSR : S ≠ R) :
    expectation p (fun x => approxComponent p J (fun y => Influence.boolValue (f y)) S x *
      approxComponent p J (fun y => Influence.boolValue (f y)) R x) ≤
      ((2:ℝ)^(3*S.card) * p^S.card) * ((2:ℝ)^(3*R.card) * p^R.card) *
        inactiveKernel p J (S ∩ R) := by
  let F := fun x => Influence.boolValue (f x)
  rw [ConditionalExpectation.local_conditional_independence hp0 hp1 S R _ _
    (approxComponent_locality p J F S) (approxComponent_locality p J F R)]
  unfold inactiveKernel
  rw [← expectation_const_mul]
  apply expectation_mono hp0.le hp1.le
  intro x
  change ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J F S)
      (restriction (S ∩ R) x) *
    ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J F R)
      (restriction (S ∩ R) x) ≤ _
  by_cases hx : J.fires (S ∩ R) x
  · rw [conditional_product_zero_of_fires hp0 hp1 J F S R hSR x hx]
    simp [hx]
  · simp only [if_neg hx]
    have ha := approxComponent_conditional_abs_le hp0 hp1 J f S (S ∩ R) (restriction (S ∩ R) x)
    have hb := approxComponent_conditional_abs_le hp0 hp1 J f R (S ∩ R) (restriction (S ∩ R) x)
    have hmass : 0 < weight p (restriction (S ∩ R) x) := weight_pos hp0 hp1 _
    calc
      _ ≤ |ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J F S)
          (restriction (S ∩ R) x)| *
        |ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J F R)
          (restriction (S ∩ R) x)| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ (((2:ℝ)^(3*S.card) * p^S.card) / weight p (restriction (S ∩ R) x)) *
          (((2:ℝ)^(3*R.card) * p^R.card) / weight p (restriction (S ∩ R) x)) :=
        mul_le_mul ha hb (abs_nonneg _) (div_nonneg (by positivity) hmass.le)
      _ = _ := by
        change _ = _ * (1 / weight p (restriction (S ∩ R) x)^2)
        field_simp

/-- Enlarging exact intersections to all common subsets only adds nonnegative terms. -/
theorem intersection_sum_le (A : Finset (Finset ι)) (a K : Finset ι → ℝ)
    (ha : ∀ S ∈ A, 0 ≤ a S) (hK : ∀ T, 0 ≤ K T) :
    (∑ S ∈ A, ∑ R ∈ A, a S * a R * K (S ∩ R)) ≤
      ∑ T : Finset ι, bMass A a T ^ 2 * K T := by
  have hpair (S R : Finset ι) (hS : S ∈ A) (hR : R ∈ A) :
      a S * a R * K (S ∩ R) ≤
      ∑ T : Finset ι, if T ⊆ S ∧ T ⊆ R then a S * a R * K T else 0 := by
    have h := Finset.single_le_sum
      (s := Finset.univ) (f := fun T : Finset ι =>
        if T ⊆ S ∧ T ⊆ R then a S * a R * K T else 0)
      (fun T _ => by
        dsimp only
        split_ifs
        · exact mul_nonneg (mul_nonneg (ha S hS) (ha R hR)) (hK T)
        · exact le_rfl)
      (Finset.mem_univ (S ∩ R))
    simpa only [Finset.inter_subset_left, Finset.inter_subset_right, and_self, if_true] using h
  calc
    _ ≤ ∑ S ∈ A, ∑ R ∈ A, ∑ T : Finset ι,
        if T ⊆ S ∧ T ⊆ R then a S * a R * K T else 0 := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro R hR
      exact hpair S R hS hR
    _ = ∑ S ∈ A, ∑ T : Finset ι, ∑ R ∈ A,
        if T ⊆ S ∧ T ⊆ R then a S * a R * K T else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_comm]
    _ = ∑ T : Finset ι, ∑ S ∈ A, ∑ R ∈ A,
        if T ⊆ S ∧ T ⊆ R then a S * a R * K T else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _
      unfold bMass
      rw [pow_two, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro R _
      by_cases hTS : T ⊆ S <;> by_cases hTR : T ⊆ R <;> simp [hTS,hTR]


/-- Reciprocal marginal mass, evaluated on the global cube. -/
theorem reciprocal_localMass_expectation {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (T : Finset ι) : expectation p (fun x : Cube ι => 1 / localMass p T x) = (2:ℝ)^T.card := by
  have h := expectation_restrict (ι := ι) p (fun i => i ∈ T)
    (fun z => 1 / weight p z)
  rw [Subsingleton.elim (Subtype.fintype (fun i => i ∈ T)) (Finset.Subtype.fintype T)] at h
  exact h.trans (reciprocal_mass_expectation hp0 hp1 T)

omit [Fintype ι] in
/-- Monotonicity of the supersets' total mass. -/
theorem bMass_mono (A : Finset (Finset ι)) (a m : Finset ι → ℝ)
    (ham : ∀ S ∈ A, a S ≤ m S) (T : Finset ι) : bMass A a T ≤ bMass A m T := by
  apply Finset.sum_le_sum
  intro S hS
  by_cases hTS : T ⊆ S <;> simp [hTS, ham S hS]

omit [Fintype ι] in
/-- Outside the arity cutoff, no retained superset can contribute mass. -/
theorem bMass_eq_zero_of_card_gt (A : Finset (Finset ι)) (a : Finset ι → ℝ) (k : ℝ)
    (hcard : ∀ S ∈ A, (S.card : ℝ) ≤ k) (T : Finset ι) (hT : k < T.card) :
    bMass A a T = 0 := by
  apply Finset.sum_eq_zero
  intro S hS
  have hTS : ¬ T ⊆ S := by
    intro h
    have hc : (T.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card h
    linarith [hcard S hS]
  simp [hTS]

/-- The threshold condition controls each overlap kernel independently of dimension. -/
theorem bMass_mul_inactiveKernel_le {p k δ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : 0 ≤ δ)
    (A : Finset (Finset ι)) (a m : Finset ι → ℝ)
    (ham : ∀ S ∈ A, a S ≤ m S) (hcard : ∀ S ∈ A, (S.card : ℝ) ≤ k)
    (T : Finset ι) :
    bMass A a T * inactiveKernel p (thresholdActivation k p δ A m) T ≤ (2:ℝ)^T.card * δ := by
  have hpoint (x : Cube ι) : bMass A a T *
      (if (thresholdActivation k p δ A m).fires T x then 0 else 1 / localMass p T x ^ 2) ≤
      δ * (1 / localMass p T x) := by
    have hmass : 0 < localMass p T x := weight_pos hp0 hp1 _
    by_cases hdeg : (T.card : ℝ) ≤ k
    · by_cases hfire : (thresholdActivation k p δ A m).fires T x
      · simp only [if_pos hfire, mul_zero]
        exact mul_nonneg hδ (one_div_nonneg.mpr hmass.le)
      · have hmass_lt : bMass A m T < δ * localMass p T x := by
          apply lt_of_not_ge
          intro h
          exact hfire ⟨hdeg,h⟩
        have hbound : bMass A a T ≤ δ * localMass p T x :=
          (bMass_mono A a m ham T).trans hmass_lt.le
        have hfrac : (bMass A a T / localMass p T x) / localMass p T x ≤ δ / localMass p T x :=
          div_le_div_of_nonneg_right ((div_le_iff₀ hmass).mpr hbound) hmass.le
        simp only [if_neg hfire]
        convert hfrac using 1 <;> field_simp
    · rw [bMass_eq_zero_of_card_gt A a k hcard T (lt_of_not_ge hdeg), zero_mul]
      exact mul_nonneg hδ (one_div_nonneg.mpr hmass.le)
  have h := expectation_mono hp0.le hp1.le hpoint
  rw [expectation_const_mul, expectation_const_mul, reciprocal_localMass_expectation hp0 hp1] at h
  simpa only [inactiveKernel, mul_comm] using h

/-- Thresholded overlap summation: all pair intersections are bounded by a
single weighted powerset count. -/
theorem intersection_kernel_sum_le {p k δ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : 0 ≤ δ)
    (A : Finset (Finset ι)) (a m : Finset ι → ℝ)
    (ha : ∀ S ∈ A, 0 ≤ a S) (ham : ∀ S ∈ A, a S ≤ m S)
    (hcard : ∀ S ∈ A, (S.card : ℝ) ≤ k) :
    (∑ S ∈ A, ∑ R ∈ A, a S * a R *
      inactiveKernel p (thresholdActivation k p δ A m) (S ∩ R)) ≤
      δ * ∑ S ∈ A, (3:ℝ)^S.card * a S := by
  apply (intersection_sum_le A a _ ha
    (inactiveKernel_nonneg hp0.le hp1.le _)).trans
  calc
    _ ≤ ∑ T : Finset ι, bMass A a T * ((2:ℝ)^T.card * δ) := by
      apply Finset.sum_le_sum
      intro T _
      have h := mul_le_mul_of_nonneg_left
        (bMass_mul_inactiveKernel_le hp0 hp1 hδ A a m ham hcard T)
        (bMass_nonneg A a ha T)
      nlinarith
    _ = δ * ∑ S ∈ A, (3:ℝ)^S.card * a S := by
      unfold bMass
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      calc
        _ = (∑ T : Finset ι, if T ⊆ S then (2:ℝ)^T.card else 0) * (δ * a S) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro T _
          by_cases hTS : T ⊆ S <;> simp [hTS]
          all_goals ring
        _ = _ := by
          rw [sum_subsets_eq, sum_powerset_two_pow]
          ring


/-- Nonnegative envelope of the off-diagonal conditional-component correlations. -/
def crossEnvelope (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (A : Finset (Finset ι)) : ℝ :=
  ∑ S ∈ A, ∑ R ∈ A, if S = R then 0 else
    max 0 (expectation p (fun x => approxComponent p J f S x * approxComponent p J f R x))

theorem crossEnvelope_nonneg (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (A : Finset (Finset ι)) : 0 ≤ crossEnvelope p J f A := by
  apply Finset.sum_nonneg
  intro S _
  apply Finset.sum_nonneg
  intro R _
  split_ifs <;> positivity

omit [Fintype ι] [DecidableEq ι] in
/-- The pairwise degree factors are controlled by the real source cutoff. -/
theorem degree_factor_le {p k : ℝ} (hp0 : 0 ≤ p) (S R : Finset ι)
    (hS : (S.card : ℝ) ≤ k) (hR : (R.card : ℝ) ≤ k) :
    ((2:ℝ)^(3*S.card) * p^S.card) * ((2:ℝ)^(3*R.card) * p^R.card) ≤
      (2:ℝ)^(6*k) * (p^S.card * p^R.card) := by
  have hpow : (2:ℝ)^(3*S.card + 3*R.card) ≤ (2:ℝ)^(6*k) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  calc
    _ = (2:ℝ)^(3*S.card + 3*R.card) * (p^S.card * p^R.card) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hp0 _))

/-- Each off-diagonal envelope term is bounded by the common-degree overlap kernel. -/
theorem crossEnvelope_le_kernel_sum {p k : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → Bool) (A : Finset (Finset ι))
    (hcard : ∀ S ∈ A, (S.card : ℝ) ≤ k) :
    crossEnvelope p J (fun x => Influence.boolValue (f x)) A ≤
      (2:ℝ)^(6*k) * ∑ S ∈ A, ∑ R ∈ A,
        p^S.card * p^R.card * inactiveKernel p J (S ∩ R) := by
  unfold crossEnvelope
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro R hR
  have hnon : 0 ≤ (2:ℝ)^(6*k) * (p^S.card * p^R.card * inactiveKernel p J (S ∩ R)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (mul_nonneg
      (mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg hp0.le _)) (inactiveKernel_nonneg hp0.le hp1.le _ _))
  by_cases hSR : S = R
  · simpa only [if_pos hSR] using hnon
  · rw [if_neg hSR]
    apply max_le hnon
    apply (pair_cross_le_kernel hp0 hp1 J f S R hSR).trans
    have h := mul_le_mul_of_nonneg_right (degree_factor_le hp0.le S R (hcard S hS) (hcard R hR))
      (inactiveKernel_nonneg hp0.le hp1.le J (S ∩ R))
    nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- The powerset factor is at most `2^(2k)` for every retained set. -/
theorem three_pow_card_le {k : ℝ} (S : Finset ι) (hS : (S.card : ℝ) ≤ k) :
    (3:ℝ)^S.card ≤ (2:ℝ)^(2*k) := by
  calc
    (3:ℝ)^S.card ≤ (4:ℝ)^S.card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (2:ℝ)^(2*(S.card:ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- The repaired complete cross envelope bound, before the final rank factor.
Every activation and retained set is the exact one from Hatami's construction. -/
theorem crossEnvelope_le_corrected {p k δ η : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 1/2) (hδ : 0 ≤ δ) (hη : 0 < η) (f : Cube ι → Bool) :
    crossEnvelope p (fourierActivation k p δ η (fun x => Influence.boolValue (f x)))
      (fun x => Influence.boolValue (f x))
      (significantSets p (fun x => Influence.boolValue (f x)) k η) ≤
        (2:ℝ)^(8*k) * δ / η^2 := by
  have hp1 : p < 1 := by linarith
  let F := fun x => Influence.boolValue (f x)
  let A := significantSets p F k η
  have hcard : ∀ S ∈ A, (S.card : ℝ) ≤ k := significantSets_card p F k η
  have ha : ∀ S ∈ A, 0 ≤ p^S.card := fun S _ => pow_nonneg hp0.le _
  have ham : ∀ S ∈ A, p^S.card ≤ componentTailMass p F η S :=
    fun S hS => pow_le_componentTailMass_of_significant hp0.le hp F S hS
  have hsum : (∑ S ∈ A, p^S.card) ≤ 1 / η^2 := by
    apply le_trans (Finset.sum_le_sum (fun S hS => ham S hS))
    exact sum_componentTailMass_le hp0 hp1 hη f A
  have hweighted : (∑ S ∈ A, (3:ℝ)^S.card * p^S.card) ≤
      (2:ℝ)^(2*k) / η^2 := by
    calc
      _ ≤ ∑ S ∈ A, (2:ℝ)^(2*k) * p^S.card := by
        apply Finset.sum_le_sum
        intro S hS
        exact mul_le_mul_of_nonneg_right (three_pow_card_le S (hcard S hS)) (ha S hS)
      _ = (2:ℝ)^(2*k) * ∑ S ∈ A, p^S.card := (Finset.mul_sum ..).symm
      _ ≤ (2:ℝ)^(2*k) * (1 / η^2) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by norm_num) _)
      _ = _ := by ring
  have hkernel := intersection_kernel_sum_le hp0 hp1 hδ A (fun S => p^S.card)
    (componentTailMass p F η) ha ham hcard
  have hcross := crossEnvelope_le_kernel_sum hp0 hp1 (fourierActivation k p δ η F) f A hcard
  apply hcross.trans
  calc
    _ ≤ (2:ℝ)^(6*k) * (δ * ∑ S ∈ A, (3:ℝ)^S.card * p^S.card) :=
      mul_le_mul_of_nonneg_left hkernel (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (2:ℝ)^(6*k) * (δ * ((2:ℝ)^(2*k) / η^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hweighted hδ) (Real.rpow_nonneg (by norm_num) _)
    _ = (2:ℝ)^(8*k) * δ / η^2 := by
      have hpow : (2:ℝ)^(6*k) * (2:ℝ)^(2*k) = (2:ℝ)^(8*k) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      calc
        _ = ((2:ℝ)^(6*k) * (2:ℝ)^(2*k)) * δ / η^2 := by ring
        _ = _ := by rw [hpow]


omit [Fintype ι] [DecidableEq ι] in
/-- Equal-cardinality distinct supports are incomparable. -/
theorem not_subset_of_card_eq {S R : Finset ι} (hcard : S.card = R.card) (hne : S ≠ R) : ¬ S ⊆ R := by
  intro hsub
  exact hne (Finset.eq_of_subset_of_card_le hsub hcard.ge)

/-- The Gram expansion of a fixed rank is controlled by the diagonal plus
its rows in the nonnegative global cross envelope. -/
theorem rank_group_residual_le (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (A : Finset (Finset ι)) (r : ℕ) :
    expectation p (fun x => (∑ S ∈ A with S.card = r,
      (Fourier.component p f S x - approxComponent p J f S x))^2) ≤
    ∑ S ∈ A with S.card = r,
      (ConditionalExpectation.squaredError (weight p) (Fourier.component p f S) (approxComponent p J f S) +
      ∑ R ∈ A, if S = R then 0 else
        max 0 (expectation p (fun x => approxComponent p J f S x * approxComponent p J f R x))) := by
  let B := A.filter (fun S => S.card = r)
  have hff : ∀ S ∈ B, ∀ R ∈ B, S ≠ R →
      ResidualGram.inner (weight p) (Fourier.component p f S) (Fourier.component p f R) = 0 := by
    intro S hS R hR hne
    have hcard : S.card = R.card := (Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hR).2.symm
    have h := component_orthogonal_of_not_subset p f S R (not_subset_of_card_eq hcard hne)
      (Fourier.component p f R) (Fourier.component_locality p f R)
    simpa only [ResidualGram.inner, expectation, mul_assoc] using h
  have hfg : ∀ S ∈ B, ∀ R ∈ B, S ≠ R →
      ResidualGram.inner (weight p) (Fourier.component p f S) (approxComponent p J f R) = 0 := by
    intro S hS R hR hne
    have hcard : S.card = R.card := (Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hR).2.symm
    have h := component_approx_orthogonal p J f S R (not_subset_of_card_eq hcard hne)
    simpa only [ResidualGram.inner, expectation, mul_assoc] using h
  change (∑ x, weight p x * (∑ S ∈ B, (Fourier.component p f S x - approxComponent p J f S x))^2) ≤ _
  rw [ResidualGram.residual_square_sum (weight p) B (Fourier.component p f) (approxComponent p J f) hff hfg]
  rw [Finset.sum_add_distrib]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro S hS
  calc
    _ ≤ ∑ R ∈ B.erase S, if S = R then 0 else
        max 0 (expectation p (fun x => approxComponent p J f S x * approxComponent p J f R x)) := by
      apply Finset.sum_le_sum
      intro R hR
      have hne : S ≠ R := Ne.symm (Finset.mem_erase.mp hR).1
      rw [if_neg hne]
      simpa only [ResidualGram.inner, expectation, mul_assoc] using
        (le_max_right 0 (expectation p (fun x => approxComponent p J f S x * approxComponent p J f R x)))
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _))
      intro R _ _
      split_ifs <;> positivity

/-- Actual residual assembly from the diagonal and the repaired cross envelope,
with an arbitrary covering set of cardinality ranks. -/
theorem residual_le_rank_factor {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Activation ι) (f : Cube ι → ℝ) (A : Finset (Finset ι))
    (ranks : Finset ℕ) (hcover : ∀ S ∈ A, S.card ∈ ranks) :
    ConditionalExpectation.squaredError (weight p) (truncated p f A) (approxTruncated p J f A) ≤
      (ranks.card : ℝ) * ((∑ S ∈ A, ConditionalExpectation.squaredError (weight p)
        (Fourier.component p f S) (approxComponent p J f S)) + crossEnvelope p J f A) := by
  have hRank := RankGrouping.weighted_squared_sum_le_rank_groups (weight p) (weight_nonneg hp0 hp1)
    A ranks Finset.card hcover (fun x S => Fourier.component p f S x - approxComponent p J f S x)
  calc
    _ = ∑ x, weight p x * (∑ S ∈ A, (Fourier.component p f S x - approxComponent p J f S x))^2 := by
      simp only [ConditionalExpectation.squaredError, truncated, approxTruncated, Finset.sum_sub_distrib]
    _ ≤ _ := hRank
    _ ≤ (ranks.card : ℝ) * ∑ r ∈ ranks, ∑ S ∈ A with S.card = r,
        (ConditionalExpectation.squaredError (weight p) (Fourier.component p f S) (approxComponent p J f S) +
          ∑ R ∈ A, if S = R then 0 else
            max 0 (expectation p (fun x => approxComponent p J f S x * approxComponent p J f R x))) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro r _
      exact rank_group_residual_le p J f A r
    _ = _ := by
      rw [← RankGrouping.sum_by_rank A ranks Finset.card hcover]
      rw [Finset.sum_add_distrib]
      rfl


/-- The rank-count factor is simultaneously at most `2k` and `2^k` for real `k >= 1`. -/
theorem rankCount_bounds {k : ℝ} (hk : 1 ≤ k) :
    ((Nat.floor k + 1 : ℕ) : ℝ) ≤ 2*k ∧ ((Nat.floor k + 1 : ℕ) : ℝ) ≤ (2:ℝ)^k := by
  have hfloor : (Nat.floor k : ℝ) ≤ k := Nat.floor_le (by linarith)
  constructor
  · push_cast
    linarith
  · calc
      ((Nat.floor k + 1 : ℕ) : ℝ) ≤ (2:ℝ)^(Nat.floor k) := by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.floor k).lt_two_pow_self)
      _ = (2:ℝ)^((Nat.floor k):ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor

/-- The low-degree small-component mass is nonnegative. -/
theorem smallMassReal_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Cube ι → ℝ) (k η : ℝ) : 0 ≤ FourierTruncation.smallMassReal p f k η := by
  apply Finset.sum_nonneg
  intro S _
  apply expectation_nonneg hp0 hp1
  intro x
  split_ifs <;> positivity

/-- Match the diagonal quantity to the source's exact real-cutoff Step II mass. -/
theorem diagonal_sum_le_smallMassReal {p k δ η : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ) :
    (∑ S ∈ significantSets p f k η,
      ConditionalExpectation.squaredError (weight p) (Fourier.component p f S)
        (approxComponent p (fourierActivation k p δ η f) f S)) ≤
      FourierTruncation.smallMassReal p f k η := by
  have h := sum_diagonal_le_small_mass (k := k) (η := η) hp0 hp1 hδ f
  apply h.trans_eq
  rw [HatamiResidual.expectation_finset_sum, Finset.sum_filter]
  unfold FourierTruncation.smallMassReal
  apply Finset.sum_congr rfl
  intro S _
  by_cases hdeg : (S.card : ℝ) ≤ k <;> simp [hdeg]

/-- Hatami's complete Step III residual estimate for the exact threshold
construction, with the repaired cross-term exponent. The only remaining
analytic quantity is the explicitly defined small-component mass. -/
theorem approxTruncated_residual_le {p k δ η : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 1/2) (hk : 1 ≤ k)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (f : Cube ι → Bool) :
    ConditionalExpectation.squaredError (weight p)
      (truncated p (fun x => Influence.boolValue (f x))
        (significantSets p (fun x => Influence.boolValue (f x)) k η))
      (approxTruncated p (fourierActivation k p δ η (fun x => Influence.boolValue (f x)))
        (fun x => Influence.boolValue (f x))
        (significantSets p (fun x => Influence.boolValue (f x)) k η)) ≤
      2*k*FourierTruncation.smallMassReal p (fun x => Influence.boolValue (f x)) k η +
        (2:ℝ)^(9*k)*δ/η^2 := by
  have hp1 : p < 1 := by linarith
  let F := fun x => Influence.boolValue (f x)
  let A := significantSets p F k η
  let J := fourierActivation k p δ η F
  let ranks := Finset.range (Nat.floor k + 1)
  have hcover : ∀ S ∈ A, S.card ∈ ranks := by
    intro S hS
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_iff.mpr (Nat.le_floor (significantSets_card p F k η S hS))
  have h := residual_le_rank_factor hp0.le hp1.le J F A ranks hcover
  have hdiag := diagonal_sum_le_smallMassReal (k := k) (η := η) hp0 hp1 hδ1 F
  have hcross := crossEnvelope_le_corrected (k := k) hp0 hp hδ0 hη f
  have hsmall0 := smallMassReal_nonneg hp0.le hp1.le F k η
  have hcross0 : 0 ≤ (2:ℝ)^(8*k)*δ/η^2 := by positivity
  have hn := rankCount_bounds hk
  have hcard : (ranks.card : ℝ) = ((Nat.floor k + 1 : ℕ) : ℝ) := by simp [ranks]
  rw [hcard] at h
  apply h.trans
  calc
    _ ≤ ((Nat.floor k + 1 : ℕ) : ℝ) *
        (FourierTruncation.smallMassReal p F k η + (2:ℝ)^(8*k)*δ/η^2) :=
      mul_le_mul_of_nonneg_left (add_le_add hdiag hcross) (Nat.cast_nonneg _)
    _ = ((Nat.floor k + 1 : ℕ) : ℝ) * FourierTruncation.smallMassReal p F k η +
        ((Nat.floor k + 1 : ℕ) : ℝ) * ((2:ℝ)^(8*k)*δ/η^2) := by ring
    _ ≤ (2*k)*FourierTruncation.smallMassReal p F k η +
        (2:ℝ)^k * ((2:ℝ)^(8*k)*δ/η^2) :=
      add_le_add (mul_le_mul_of_nonneg_right hn.1 hsmall0)
        (mul_le_mul_of_nonneg_right hn.2 hcross0)
    _ = _ := by
      have hpow : (2:ℝ)^k * (2:ℝ)^(8*k) = (2:ℝ)^(9*k) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      calc
        _ = 2*k*FourierTruncation.smallMassReal p F k η +
          ((2:ℝ)^k * (2:ℝ)^(8*k))*δ/η^2 := by ring
        _ = _ := by rw [hpow]

end NarrowDNF.HatamiCrossTerms




