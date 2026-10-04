import NarrowDNF.Fourier
import NarrowDNF.ConditionalExpectation
import NarrowDNF.BiasedHypercontractivity
import NarrowDNF.JuntaCounting
import NarrowDNF.AllBiasReduction
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Fourier support projection for a biased junta approximation

This file proves the dimension- and bias-uniform compact-bias monotone junta
theorem. Its analytic input is derived in BiasedHypercontractivity, rather than
postulated as an external theorem.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.BiasedFriedgut
open ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite biased Fourier polynomial specified by its coefficient array. -/
def synthesize (p : ℝ) (c : Finset ι → ℝ) (x : Cube ι) : ℝ :=
  ∑ S : Finset ι, c S * Fourier.setCharacter p S x

/-- Orthogonality of the subset-indexed basis. -/
theorem set_orthogonality {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S T : Finset ι) :
    expectation p (fun x => Fourier.setCharacter p S x * Fourier.setCharacter p T x) =
      if S = T then 1 else 0 := by
  simpa only [Fourier.setCharacter, Equiv.apply_eq_iff_eq] using
    Fourier.orthogonality hp0 hp1 (Fourier.maskEquivFinset.symm S) (Fourier.maskEquivFinset.symm T)

/-- Synthesis recovers exactly the coefficient array used to define it. -/
theorem coefficient_synthesize {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (c : Finset ι → ℝ) (T : Finset ι) :
    Fourier.setCoefficient p (synthesize p c) T = c T := by
  change expectation p (fun x => synthesize p c x * Fourier.setCharacter p T x) = c T
  calc
    _ = expectation p (fun x => ∑ S : Finset ι,
        c S * (Fourier.setCharacter p S x * Fourier.setCharacter p T x)) := by
      congr 1
      funext x
      unfold synthesize
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = ∑ S : Finset ι, c S * expectation p
        (fun x => Fourier.setCharacter p S x * Fourier.setCharacter p T x) := by
      rw [expectation_sum]
      simp_rw [expectation_const_mul]
    _ = c T := by simp_rw [set_orthogonality hp0 hp1]; simp

/-- Reconstructing from every subset coefficient gives the original function. -/
theorem synthesize_coefficients {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (F : Cube ι → ℝ) (x : Cube ι) :
    synthesize p (Fourier.setCoefficient p F) x = F x := by
  calc
    _ = ∑ s : Cube ι, Fourier.coefficient p F s * Fourier.character p s x := by
      symm
      apply Fintype.sum_equiv Fourier.maskEquivFinset
      intro s
      simp [Fourier.setCoefficient, Fourier.setCharacter]
    _ = F x := Fourier.expansion hp0 hp1 F x

theorem setCoefficient_sub (p : ℝ) (F G : Cube ι → ℝ) (S : Finset ι) :
    Fourier.setCoefficient p (fun x => F x - G x) S =
      Fourier.setCoefficient p F S - Fourier.setCoefficient p G S := by
  simp [Fourier.setCoefficient, Fourier.coefficient, sub_mul, Fourier.expectation_sub]

/-- Keep precisely the Fourier components whose support lies inside J. -/
def projection (p : ℝ) (J : Finset ι) (F : Cube ι → ℝ) : Cube ι → ℝ :=
  synthesize p (fun S => if S ⊆ J then Fourier.setCoefficient p F S else 0)

/-- The spectral projection reads only the selected coordinates. -/
theorem projection_locality (p : ℝ) (J : Finset ι) (F : Cube ι → ℝ)
    (x y : Cube ι) (hxy : ∀ i ∈ J, x i = y i) :
    projection p J F x = projection p J F y := by
  unfold projection synthesize
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S ⊆ J
  · simp only [if_pos hS]
    rw [Fourier.setCharacter_locality p S x y (fun i hi => hxy i (hS hi))]
  · simp [hS]

/-- Exact squared residual of the coordinate-supported Fourier projection. -/
theorem projection_squared_error {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Finset ι) (F : Cube ι → ℝ) :
    expectation p (fun x => (F x - projection p J F x)^2) =
      ∑ S : Finset ι, if S ⊆ J then 0 else (Fourier.setCoefficient p F S)^2 := by
  rw [Fourier.parseval_finset hp0 hp1]
  apply Finset.sum_congr rfl
  intro S _
  rw [setCoefficient_sub, projection, coefficient_synthesize hp0 hp1]
  split_ifs <;> simp_all

/-- The Bayes-optimal J-junta has error controlled by Fourier mass outside J.
This theorem imposes no monotonicity assumption on the target. -/
theorem coordinate_decoder_spectral_error {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Finset ι) (f : Cube ι → Bool) :
    error p f
      (ConditionalExpectation.decoder (fun x : Cube ι => fun i : {i // i ∈ J} => x i)
        (weight p) f) ≤
      4 * ∑ S : Finset ι, if S ⊆ J then 0 else
        (Fourier.setCoefficient p (fun x => ConditionalExpectation.value (f x)) S)^2 := by
  let φ := fun x : Cube ι => fun i : {i // i ∈ J} => x i
  let F := fun x => ConditionalExpectation.value (f x)
  have hround := ConditionalExpectation.decoder_error_le_four φ (weight p)
    (weight_nonneg hp0.le hp1.le) f
  have hproj := ConditionalExpectation.squaredError_minimal_of_measurable φ (weight p) F
    (projection p J F) (weight_pos hp0 hp1) (by
      intro x y hxy
      apply projection_locality
      intro i hi
      exact congrFun hxy (⟨i,hi⟩ : {i // i ∈ J}))
  have hbound := hround.trans (mul_le_mul_of_nonneg_left hproj (by norm_num : (0:ℝ) ≤ 4))
  have herr : ConditionalExpectation.booleanError (weight p) f
      (ConditionalExpectation.decoder φ (weight p) f) =
        error p f (ConditionalExpectation.decoder φ (weight p) f) := by
    simp [ConditionalExpectation.booleanError, error, probability, expectation]
  rw [herr] at hbound
  change error p f (ConditionalExpectation.decoder φ (weight p) f) ≤
    4 * expectation p (fun x => (F x - projection p J F x)^2) at hbound
  rw [projection_squared_error hp0 hp1] at hbound
  exact hbound

/-- If the target is increasing, the same spectral bound is achieved by an
increasing Boolean function on the selected coordinates. -/
theorem exists_monotone_junta_of_spectral_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Finset ι) (f : Cube ι → Bool) (hf : Monotone f) :
    ∃ g : Cube ι → Bool, Monotone g ∧
      (∀ x y, (∀ i ∈ J, x i = y i) → g x = g y) ∧
      error p f g ≤ 4 * ∑ S : Finset ι, if S ⊆ J then 0 else
        (Fourier.setCoefficient p (fun x => ConditionalExpectation.value (f x)) S)^2 := by
  let φ := fun x : Cube ι => fun i : {i // i ∈ J} => x i
  refine ⟨ConditionalExpectation.decoder φ (weight p) f, ?_, ?_,
    coordinate_decoder_spectral_error hp0 hp1 J f⟩
  · intro x y hxy
    apply ConditionalExpectation.threshold_monotone
    let P : ι → Prop := fun i => i ∈ J
    let F := fun x => ConditionalExpectation.value (f x)
    change ConditionalExpectation.mean φ (weight p) F (φ x) ≤
      ConditionalExpectation.mean φ (weight p) F (φ y)
    have hmono := ConditionalExpectation.mean_restriction_monotone (ι := ι) hp0 hp1 P f hf
    have hzx : (fun i : {i // P i} => x i) ≤ (fun i : {i // P i} => y i) := fun i => hxy i
    have hm := hmono hzx
    simp only [← ConditionalExpectation.mean_decidableEq_irrel
      (α := Cube ι) (β := ({i // i ∈ J} → Bool))
      (inferInstance : DecidableEq ({i // i ∈ J} → Bool))] at hm
    exact hm
  · intro x y hxy
    apply ConditionalExpectation.decoder_eq_of_atom_eq
    funext i
    exact hxy i i.property

/-- The L(4/3) residual moment on a Boolean fiber is at most its pivotal indicator. -/
theorem boolean_fiber_residual_moment_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a b : Bool) :
    (1-p)*|Influence.boolValue a - ((1-p)*Influence.boolValue a+p*Influence.boolValue b)|^(4/3:ℝ) +
      p*|Influence.boolValue b - ((1-p)*Influence.boolValue a+p*Influence.boolValue b)|^(4/3:ℝ) ≤
        FiberShift.mismatch a b := by
  have hpbar : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hpbar1 : 1-p ≤ 1 := by linarith
  have hpPow : p^(4/3:ℝ) ≤ 1 := Real.rpow_le_one hp0 hp1 (by norm_num)
  have hqPow : (1-p)^(4/3:ℝ) ≤ 1 := Real.rpow_le_one hpbar hpbar1 (by norm_num)
  have hpMul := mul_le_mul_of_nonneg_left hpPow hpbar
  have hqMul := mul_le_mul_of_nonneg_left hqPow hp0
  cases a <;> cases b <;>
    simp [Influence.boolValue, FiberShift.mismatch, abs_of_nonneg hp0, abs_of_nonneg hpbar,
      abs_of_nonpos (by linarith : p-1 ≤ 0)] <;> nlinarith

/-- Boolean coordinate residuals have small fractional moment controlled by
pivotal probability, uniformly over the bias. -/
theorem residual_moment43_le_pivotal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Cube ι → Bool) (i : ι) :
    BourgainDuality.moment43 (weight p)
      (Fourier.coordinateResidual p (fun x => Influence.boolValue (f x)) i) ≤
        Influence.pivotalProbability p f i := by
  change expectation p (fun x =>
    |Fourier.coordinateResidual p (fun x => Influence.boolValue (f x)) i x|^(4/3:ℝ)) ≤ _
  rw [expectation_split p i]
  unfold Influence.pivotalProbability
  rw [← expectation_const_mul, ← expectation_const_mul, ← expectation_add]
  apply expectation_mono hp0 hp1
  intro z
  simpa only [Fourier.coordinateResidual, Fourier.coordinateMean, Influence.update_insertBit] using
    boolean_fiber_residual_moment_le p hp0 hp1 (f (insertBit i false z)) (f (insertBit i true z))

/-- Squared stable influence is bounded by the cube of pivotal probability.
The polynomial form avoids introducing an unproved fractional-power estimate. -/
theorem stable_residual_energy_sq_le (lam p : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1/2)
    (hp0 : lam ≤ p) (hp1 : p ≤ 1-lam) (f : Cube ι → Bool) (i : ι) :
    (expectation p (fun x =>
      BourgainNoise.tensorNoise p (fun _ => lam/4)
        (Fourier.coordinateResidual p (fun x => Influence.boolValue (f x)) i) x ^ 2))^2 ≤
          (Influence.pivotalProbability p f i)^3 := by
  have h := BiasedHypercontractivity.biased_spectral_contract43 lam p hlam0 hlam1 hp0 hp1
    (Fourier.coordinateResidual p (fun x => Influence.boolValue (f x)) i)
  have hm := residual_moment43_le_pivotal p (hlam0.le.trans hp0) (by linarith) f i
  exact h.trans (pow_le_pow_left₀
    (BourgainDuality.moment43_nonneg _ _ (weight_nonneg (hlam0.le.trans hp0) (by linarith))) hm 3)

omit [DecidableEq ι] in
theorem constant_mask_product (ρ : ℝ) (s : Cube ι) :
    (∏ i, if s i then ρ else 1) = ρ^(Fourier.degree s) := by
  rw [← Finset.prod_filter]
  simp [Fourier.degree]

/-- Stable-energy expression for a noised coordinate residual. -/
theorem stable_residual_spectral {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ℝ) (F : Cube ι → ℝ) (i : ι) :
    expectation p (fun x => BourgainNoise.tensorNoise p (fun _ => ρ)
      (Fourier.coordinateResidual p F i) x ^ 2) =
        JuntaCounting.stableEnergy (ρ^2) (fun S => (Fourier.setCoefficient p F S)^2) i := by
  rw [BourgainNoise.tensorNoise_secondMoment hp0 hp1]
  simp_rw [constant_mask_product, Fourier.coefficient_coordinateResidual]
  unfold JuntaCounting.stableEnergy
  apply Fintype.sum_equiv Fourier.maskEquivFinset
  intro s
  simp only [Fourier.setCoefficient, Equiv.symm_apply_apply]
  by_cases hs : s i = true
  · simp only [hs, if_true]
    have hmem : i ∈ Fourier.maskEquivFinset s := by simp [Fourier.maskEquivFinset,hs]
    simp only [hmem, if_true, mul_pow]
    have hdeg : (Fourier.maskEquivFinset s).card = Fourier.degree s := rfl
    rw [hdeg, ← pow_mul, Nat.mul_comm, pow_mul]
  · have hfalse : s i = false := Bool.eq_false_iff.mpr hs
    simp [hfalse, Fourier.maskEquivFinset]

/-- The squared stable-energy bound in subset-indexed Fourier form. -/
theorem stableEnergy_sq_le (lam p : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1/2)
    (hp0 : lam ≤ p) (hp1 : p ≤ 1-lam) (f : Cube ι → Bool) (i : ι) :
    (JuntaCounting.stableEnergy ((lam/4)^2)
      (fun S => (Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S)^2) i)^2 ≤
        (Influence.pivotalProbability p f i)^3 := by
  have h := stable_residual_energy_sq_le lam p hlam0 hlam1 hp0 hp1 f i
  rw [stable_residual_spectral (hlam0.trans_le hp0) (by linarith)] at h
  exact h

theorem pivotal_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Cube ι → Bool) (i : ι) :
    0 ≤ Influence.pivotalProbability p f i := by
  apply expectation_nonneg hp0 hp1
  intro z
  unfold FiberShift.mismatch
  split_ifs <;> norm_num

/-- Exact normalization between total resampling influence and total pivotal mass. -/
theorem totalInfluence_eq_pivotal_sum (p : ℝ) (f : Cube ι → Bool) :
    Influence.totalInfluence p f = 2*p*(1-p)*(∑ i, Influence.pivotalProbability p f i) := by
  unfold Influence.totalInfluence
  simp_rw [Influence.resamplingInfluence_eq]
  rw [Finset.mul_sum]

/-- A dimension-free total pivotal bound on a compact bias interval. -/
theorem pivotal_sum_bound (lam p K : ℝ) (hlam0 : 0 < lam)
    (hp0 : lam ≤ p) (hp1 : p ≤ 1-lam) (f : Cube ι → Bool)
    (hI : Influence.totalInfluence p f ≤ K) :
    (∑ i, Influence.pivotalProbability p f i) ≤ K/(2*lam^2) := by
  have hpnonneg : 0 ≤ p := hlam0.le.trans hp0
  have hple : p ≤ 1 := by linarith
  have hsum : 0 ≤ ∑ i, Influence.pivotalProbability p f i :=
    Finset.sum_nonneg fun i _ => pivotal_nonneg p hpnonneg hple f i
  have ht : lam^2 ≤ p*(1-p) := by
    have := mul_le_mul hp0 (show lam ≤ 1-p by linarith) hlam0.le hpnonneg
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right ht hsum
  rw [totalInfluence_eq_pivotal_sum] at hI
  apply (le_div_iff₀ (by positivity : 0 < 2*lam^2)).mpr
  nlinarith

/-- The compact-bias monotone junta theorem, with one bound chosen before both
the dimension and the bias. This proof supplies the external high-bias input
rather than assuming it. -/
theorem compactBiasMonotoneJunta : NarrowDNF.CompactBiasMonotoneJunta := by
  intro lam K ε hlam0 hlam1 hK hε _
  let L : ℝ := K/(2*lam^2)
  let θ : ℝ := (lam/4)^2
  let k : ℕ := Nat.ceil (4*K/ε)
  let τ : ℝ := ε*θ^k/(8*L)
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hθpos : 0 < θ := by dsimp [θ]; positivity
  have hθone : θ ≤ 1 := by dsimp [θ]; nlinarith [sq_nonneg lam]
  have hτpos : 0 < τ := by dsimp [τ]; positivity
  have hparameter : τ*L/θ^k = ε/8 := by
    dsimp [τ]
    field_simp
  have hk : 4*K/ε ≤ (k:ℝ) := Nat.le_ceil _
  have hk' : 4*K ≤ (k:ℝ)*ε := (div_le_iff₀ hε).mp hk
  refine ⟨Nat.ceil (L/τ^2), ?_⟩
  intro n p hp0 hp1 f hf hI
  have hpPos : 0 < p := hlam0.trans_le hp0
  have hpLt : p < 1 := by linarith
  let P : Fin n → ℝ := Influence.pivotalProbability p f
  let e : Finset (Fin n) → ℝ := fun S =>
    (Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S)^2
  let J : Finset (Fin n) := JuntaCounting.selected τ P
  have hP : ∀ i, 0 ≤ P i := pivotal_nonneg p hpPos.le hpLt.le f
  have he : ∀ S, 0 ≤ e S := fun S => sq_nonneg _
  have hsumP : ∑ i, P i ≤ L := pivotal_sum_bound lam p K hlam0 hp0 hp1 f hI
  have hcard : J.card ≤ Nat.ceil (L/τ^2) := by
    have h := JuntaCounting.selected_card_bound τ L hτpos P hP hsumP
    exact_mod_cast h.trans (Nat.le_ceil _)
  have hstable : ∀ i, (JuntaCounting.stableEnergy θ e i)^2 ≤ (P i)^3 :=
    stableEnergy_sq_le lam p hlam0 hlam1 hp0 hp1 f
  have hsmall : ∀ i, i ∉ J → JuntaCounting.stableEnergy θ e i ≤ τ*P i := by
    intro i hi
    exact JuntaCounting.stableEnergy_le_cutoff θ τ hθpos.le hτpos.le e he P hP hstable i hi
  have hlow : (∑ S : Finset (Fin n), if S.card ≤ k ∧ ¬ S ⊆ J then e S else 0) ≤ ε/8 := by
    have h := JuntaCounting.lowDegree_outside_bound θ τ L hθpos hθone hτpos.le k J e he P hP hsumP hsmall
    simpa only [hparameter] using h
  have hhigh : (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => k < S.card), e S) ≤ ε/8 := by
    calc
      _ ≤ Influence.totalInfluence p f / (2*(k+1:ℕ)) :=
        Fourier.highDegree_mass_le_finset hpPos hpLt f k
      _ ≤ K / (2*(k+1:ℕ)) := div_le_div_of_nonneg_right hI (by positivity)
      _ ≤ ε/8 := by
        apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(k+1:ℕ))).mpr
        norm_num only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        nlinarith
  have houtside : (∑ S : Finset (Fin n), if S ⊆ J then 0 else e S) ≤ ε/4 := by
    have h := JuntaCounting.outside_mass_le_split k J e he
    linarith
  obtain ⟨g,hg,hlocal,herr⟩ := exists_monotone_junta_of_spectral_mass hpPos hpLt J f hf
  refine ⟨J,g,hcard,hg,hlocal,?_⟩
  have herr' : error p f g ≤ 4 * ∑ S : Finset (Fin n), if S ⊆ J then 0 else e S := herr
  linarith

end NarrowDNF.BiasedFriedgut
