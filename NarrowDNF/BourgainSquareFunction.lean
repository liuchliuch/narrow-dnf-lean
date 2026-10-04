import NarrowDNF.BourgainNoise
import NarrowDNF.BourgainComponents
import NarrowDNF.UniformHypercontractivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dimension-free low-degree square functions

This file derives the square functions needed in Bourgain's argument from
actual signed-noise contractions and the proved uniform-cube Bonami theorem.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainSquareFunction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Synthesis in the finite biased orthonormal basis. -/
def synthesis (p : ℝ) (a : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ s, a s * Fourier.character p s x

/-- Fourier coefficients of a synthesized expansion are its actual coefficients. -/
theorem coefficient_synthesis {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (a : (ι → Bool) → ℝ) (s : ι → Bool) :
    Fourier.coefficient p (synthesis p a) s = a s := by
  unfold Fourier.coefficient synthesis
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Influence.expectation_sum]
  simp_rw [ProductMeasure.expectation_const_mul, Fourier.orthogonality hp0 hp1]
  simp

/-- Fourier coefficients of spectral noise have the advertised multiplier. -/
theorem coefficient_tensorNoise {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ι → ℝ) (f : (ι → Bool) → ℝ) (s : ι → Bool) :
    Fourier.coefficient p (BourgainNoise.tensorNoise p ρ f) s =
      (∏ i, if s i then ρ i else 1) * Fourier.coefficient p f s :=
  coefficient_synthesis hp0 hp1 _ s

omit [DecidableEq ι] in
/-- Constant-coordinate multipliers are degree powers. -/
theorem product_constant_mask (ρ : ℝ) (s : ι → Bool) :
    (∏ i, if s i then ρ else 1) = ρ ^ Fourier.degree s := by
  simp [Fourier.degree, ← Finset.prod_filter]

/-- The normalized unbiased bit takes the values minus and plus one. -/
theorem standardBit_half (b : Bool) : Fourier.standardBit (1/2) b = if b then 1 else -1 := by
  cases b <;> norm_num [Fourier.standardBit]

/-- Signed noise on the original cube, parametrized by a separate unbiased cube. -/
def signedNoise (p : ℝ) (f : (ι → Bool) → ℝ) (y x : ι → Bool) : ℝ :=
  BourgainNoise.tensorNoise p (fun i => Fourier.standardBit (1/2) (y i) / 3) f x

omit [DecidableEq ι] in
/-- Factor the signed multiplier into its degree decay and a Walsh character. -/
theorem signed_multiplier (s y : ι → Bool) :
    (∏ i, if s i then Fourier.standardBit (1/2) (y i) / 3 else 1) =
      (1/3 : ℝ) ^ Fourier.degree s * Fourier.character (1/2) s y := by
  rw [← product_constant_mask]
  unfold Fourier.character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [Fourier.bitBasis]; ring

/-- In the sign coordinates, the signed-noise expansion has explicit
coefficients equal to the original pointwise components times the decay. -/
theorem signedNoise_eq_synthesis (p : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    (fun y => signedNoise p f y x) = synthesis (1/2)
      (fun s => (1/3 : ℝ) ^ Fourier.degree s *
        (Fourier.coefficient p f s * Fourier.character p s x)) := by
  funext y
  unfold signedNoise BourgainNoise.tensorNoise synthesis
  apply Finset.sum_congr rfl
  intro s _
  rw [signed_multiplier]
  ring

theorem signedNoise_coefficient (p : ℝ) (f : (ι → Bool) → ℝ) (s x : ι → Bool) :
    Fourier.coefficient (1/2) (fun y => signedNoise p f y x) s =
      (1/3 : ℝ) ^ Fourier.degree s *
        (Fourier.coefficient p f s * Fourier.character p s x) := by
  rw [signedNoise_eq_synthesis]
  exact coefficient_synthesis (by norm_num) (by norm_num) _ _

/-- For every fixed choice of the signs, the fourth moment contracts. -/
theorem signedNoise_fourth_contraction {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (y : ι → Bool) :
    ProductMeasure.expectation p (fun x => signedNoise p f y x ^ 4) ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  apply BourgainNoise.tensorNoise_fourth_contraction hp0 hp1
  intro i
  rw [standardBit_half]
  cases y i <;> norm_num

/-- The L(4/3) contraction holds separately for every sign choice. -/
theorem signedNoise_moment43_contraction {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (y : ι → Bool) :
    BourgainDuality.moment43 (ProductMeasure.weight p) (signedNoise p f y) ≤
      BourgainDuality.moment43 (ProductMeasure.weight p) f := by
  apply BourgainNoise.tensorNoise_moment43_contraction hp0 hp1
  intro i
  rw [standardBit_half]
  cases y i <;> norm_num

/-- Squared low-degree square function. -/
def squareFunction (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (x : ι → Bool) : ℝ :=
  ∑ s ∈ (Finset.univ.filter fun s => Fourier.degree s ≤ k),
    (Fourier.coefficient p f s * Fourier.character p s x)^2

theorem squareFunction_nonneg (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (x : ι → Bool) :
    0 ≤ squareFunction p f k x := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The square function is controlled by any fixed geometric damping of the
full nonnegative component sum. -/
theorem low_degree_le_damped (a : (ι → Bool) → ℝ) (k m : ℕ) :
    (∑ s ∈ (Finset.univ.filter fun s => Fourier.degree s ≤ k), a s^2) ≤
      (3 : ℝ)^(m*k) * ∑ s, a s^2 / (3 : ℝ)^(m * Fourier.degree s) := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ s ∈ (Finset.univ.filter fun s => Fourier.degree s ≤ k),
        (3 : ℝ)^(m*k) * (a s^2 / (3 : ℝ)^(m * Fourier.degree s)) := by
      apply Finset.sum_le_sum
      intro s hs
      have hdeg := (Finset.mem_filter.mp hs).2
      have hpow : (3 : ℝ)^(m * Fourier.degree s) ≤ (3 : ℝ)^(m*k) :=
        pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left m hdeg)
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hpow (sq_nonneg (a s))]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => by positivity)

/-- Second sign moment of signed noise, exactly. -/
theorem signedNoise_second_moment (p : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    ProductMeasure.expectation (1/2) (fun y => signedNoise p f y x ^ 2) =
      ∑ s, (Fourier.coefficient p f s * Fourier.character p s x)^2 /
        (3 : ℝ)^(2 * Fourier.degree s) := by
  rw [Fourier.parseval (by norm_num) (by norm_num)]
  apply Finset.sum_congr rfl
  intro s _
  rw [signedNoise_coefficient]
  simp only [mul_pow, div_pow, one_pow]
  rw [← pow_mul, Nat.mul_comm (Fourier.degree s) 2]
  ring

/-- Sharp uniform Bonami adds one more factor of 1/3 per coordinate to the
second moment in the sign variables. -/
theorem signedNoise_sharp_second_moment (p : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    ProductMeasure.expectation (1/2) (fun y =>
      BourgainNoise.tensorNoise (1/2) (fun _ => Hypercontractivity.sharpRho)
        (fun z => signedNoise p f z x) y ^ 2) =
      ∑ s, (Fourier.coefficient p f s * Fourier.character p s x)^2 /
        (3 : ℝ)^(3 * Fourier.degree s) := by
  rw [Fourier.parseval (by norm_num) (by norm_num)]
  apply Finset.sum_congr rfl
  intro s _
  rw [coefficient_tensorNoise (by norm_num) (by norm_num), product_constant_mask,
    signedNoise_coefficient, mul_pow, mul_pow]
  have hrho : (Hypercontractivity.sharpRho ^ Fourier.degree s)^2 =
      (1/3 : ℝ)^Fourier.degree s := by
    rw [← pow_mul, Nat.mul_comm (Fourier.degree s) 2, pow_mul,
      Hypercontractivity.sharpRho_sq]
  rw [hrho]
  simp only [div_pow, one_pow]
  have hpow : (3 : ℝ)^(3 * Fourier.degree s) =
      (3 : ℝ)^Fourier.degree s * ((3 : ℝ)^Fourier.degree s)^2 := by
    rw [Nat.mul_comm 3, pow_mul]
    ring
  rw [hpow]
  field_simp

/-- A finite-probability Jensen inequality, derived by Cauchy–Schwarz. -/
theorem secondMoment_sq_le_fourthMoment {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → ℝ) :
    (ProductMeasure.expectation p (fun x => f x ^ 2))^2 ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun x : ι → Bool => ProductMeasure.weight p x * f x^2)
    (f := fun x => ProductMeasure.weight p x * f x^4)
    (g := fun x => ProductMeasure.weight p x)
    (fun x _ => mul_nonneg (ProductMeasure.weight_nonneg hp0 hp1 x) (by positivity))
    (fun x _ => ProductMeasure.weight_nonneg hp0 hp1 x)
    (fun x _ => by ring)
  simpa only [ProductMeasure.sum_weight, mul_one] using h

/-- Finite Fubini for independent cubes with possibly different biases. -/
theorem expectation_comm (p q : ℝ) (F : (ι → Bool) → (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => ProductMeasure.expectation q (F x)) =
      ProductMeasure.expectation q (fun y => ProductMeasure.expectation p (fun x => F x y)) := by
  unfold ProductMeasure.expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Dimension-free fourth moment of the low-degree square function. This is
an actual theorem for every real-valued function, uniform in the bias. -/
theorem squareFunction_fourth {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (k : ℕ) :
    ProductMeasure.expectation p (fun x => squareFunction p f k x ^ 2) ≤
      (3 : ℝ)^(4*k) * ProductMeasure.expectation p (fun x => f x ^ 4) := by
  have hpoint (x : ι → Bool) : squareFunction p f k x ^ 2 ≤
      (3 : ℝ)^(4*k) * ProductMeasure.expectation (1/2) (fun y => signedNoise p f y x ^ 4) := by
    have hd := low_degree_le_damped
      (fun s => Fourier.coefficient p f s * Fourier.character p s x) k 2
    rw [← signedNoise_second_moment] at hd
    have hs := pow_le_pow_left₀ (squareFunction_nonneg p f k x) hd 2
    rw [mul_pow, ← pow_mul] at hs
    have hpow : 2*k*2 = 4*k := by omega
    rw [hpow] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left
      (secondMoment_sq_le_fourthMoment (by norm_num) (by norm_num) _)
      (by positivity))
  calc
    _ ≤ ProductMeasure.expectation p (fun x =>
        (3 : ℝ)^(4*k) * ProductMeasure.expectation (1/2) (fun y => signedNoise p f y x ^ 4)) :=
      ProductMeasure.expectation_mono hp0.le hp1.le hpoint
    _ = (3 : ℝ)^(4*k) * ProductMeasure.expectation (1/2)
        (fun y => ProductMeasure.expectation p (fun x => signedNoise p f y x ^ 4)) := by
      rw [ProductMeasure.expectation_const_mul, expectation_comm]
    _ ≤ (3 : ℝ)^(4*k) * ProductMeasure.expectation (1/2)
        (fun _ : ι → Bool => ProductMeasure.expectation p (fun x => f x ^ 4)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact ProductMeasure.expectation_mono (by norm_num) (by norm_num)
        (signedNoise_fourth_contraction hp0 hp1 f)
    _ = _ := by rw [ProductMeasure.expectation_const]

/-- Pointwise sign-space Bonami estimate for the low-degree square function. -/
theorem squareFunction_rpow_le_sign_moment43
    (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (x : ι → Bool) :
    squareFunction p f k x ^ (2/3 : ℝ) ≤ (3 : ℝ)^(2*k) *
      BourgainDuality.moment43 (ProductMeasure.weight (1/2)) (fun y => signedNoise p f y x) := by
  let A := BourgainDuality.moment43 (ProductMeasure.weight (1/2))
    (fun y => signedNoise p f y x)
  let L := ∑ s, (Fourier.coefficient p f s * Fourier.character p s x)^2 /
    (3 : ℝ)^(3 * Fourier.degree s)
  have hA : 0 ≤ A := BourgainDuality.moment43_nonneg _ _
    (ProductMeasure.weight_nonneg (by norm_num) (by norm_num))
  have hd := low_degree_le_damped
    (fun s => Fourier.coefficient p f s * Fourier.character p s x) k 3
  have hs := pow_le_pow_left₀ (squareFunction_nonneg p f k x) hd 2
  have hb := Hypercontractivity.uniform_spectral_sharp43 (fun y => signedNoise p f y x)
  rw [signedNoise_sharp_second_moment] at hb
  have hbound : squareFunction p f k x ^ 2 ≤ (3 : ℝ)^(6*k) * A^3 := by
    rw [mul_pow, ← pow_mul] at hs
    have he : 3*k*2 = 6*k := by omega
    rw [he] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  apply le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (mul_nonneg (by positivity) hA)
  rw [← Real.rpow_mul_natCast (squareFunction_nonneg p f k x), mul_pow,
    ← pow_mul]
  have he : 2*k*3 = 6*k := by omega
  rw [he]
  norm_num only at *
  simpa only [Real.rpow_two] using hbound

/-- Dimension-free L(4/3) moment of the low-degree square function. The RHS
contains the original function, with no assumed spectral or analytic estimate. -/
theorem squareFunction_moment43 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (k : ℕ) :
    ProductMeasure.expectation p (fun x => squareFunction p f k x ^ (2/3 : ℝ)) ≤
      (3 : ℝ)^(2*k) * BourgainDuality.moment43 (ProductMeasure.weight p) f := by
  calc
    _ ≤ ProductMeasure.expectation p (fun x => (3 : ℝ)^(2*k) *
        BourgainDuality.moment43 (ProductMeasure.weight (1/2)) (fun y => signedNoise p f y x)) :=
      ProductMeasure.expectation_mono hp0.le hp1.le
        (squareFunction_rpow_le_sign_moment43 p f k)
    _ = (3 : ℝ)^(2*k) * ProductMeasure.expectation (1/2) (fun y =>
        BourgainDuality.moment43 (ProductMeasure.weight p) (signedNoise p f y)) := by
      rw [ProductMeasure.expectation_const_mul]
      congr 1
      exact expectation_comm p (1/2) (fun x y => |signedNoise p f y x| ^ (4/3 : ℝ))
    _ ≤ (3 : ℝ)^(2*k) * ProductMeasure.expectation (1/2)
        (fun _ : ι → Bool => BourgainDuality.moment43 (ProductMeasure.weight p) f) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact ProductMeasure.expectation_mono (by norm_num) (by norm_num)
        (signedNoise_moment43_contraction hp0 hp1 f)
    _ = _ := by rw [ProductMeasure.expectation_const]

/-- Subset-indexed version of the actual square function. -/
theorem squareFunction_eq_finset (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (x : ι → Bool) :
    squareFunction p f k x =
      ∑ S ∈ (Finset.univ.filter fun S : Finset ι => S.card ≤ k),
        Fourier.component p f S x ^ 2 := by
  unfold squareFunction
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv Fourier.maskEquivFinset
  intro s
  simp only [Fourier.component, Fourier.setCoefficient, Fourier.setCharacter,
    Equiv.symm_apply_apply]
  rfl

/-- Coordinate differentiation keeps precisely the Fourier components containing
that coordinate. -/
theorem component_coordinateResidual (p : ℝ) (f : (ι → Bool) → ℝ)
    (i : ι) (S : Finset ι) (x : ι → Bool) :
    Fourier.component p (Fourier.coordinateResidual p f i) S x =
      if i ∈ S then Fourier.component p f S x else 0 := by
  unfold Fourier.component Fourier.setCoefficient
  rw [Fourier.coefficient_coordinateResidual]
  have hmask : Fourier.maskEquivFinset.symm S i = decide (i ∈ S) := rfl
  rw [hmask]
  by_cases hi : i ∈ S <;> simp [hi]

/-- The coordinate square function is the square function of the coordinate
residual. This is the bridge needed to charge its moment to influence. -/
theorem coordinateSquare_eq_residual (p : ℝ) (f : (ι → Bool) → ℝ)
    (k : ℕ) (i : ι) (x : ι → Bool) :
    BourgainComponents.coordinateSquare
      (Finset.univ.filter fun S : Finset ι => S.card ≤ k)
      (fun S => Fourier.component p f S x) i =
        squareFunction p (Fourier.coordinateResidual p f i) k x := by
  rw [squareFunction_eq_finset]
  unfold BourgainComponents.coordinateSquare
  apply Finset.sum_congr rfl
  intro S _
  rw [component_coordinateResidual]
  split_ifs <;> simp

omit [Fintype ι] in
/-- A bounded function has coordinate residual bounded in absolute value by one. -/
theorem coordinateResidual_abs_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (i : ι) (x : ι → Bool) : |Fourier.coordinateResidual p f i x| ≤ 1 := by
  have hp' : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hm0 : 0 ≤ Fourier.coordinateMean p f i x :=
    add_nonneg (mul_nonneg hp' (hf0 _)) (mul_nonneg hp0 (hf0 _))
  have hm1 : Fourier.coordinateMean p f i x ≤ 1 := by
    have ha := mul_le_mul_of_nonneg_left (hf1 (Function.update x i false)) hp'
    have hb := mul_le_mul_of_nonneg_left (hf1 (Function.update x i true)) hp0
    unfold Fourier.coordinateMean
    nlinarith
  unfold Fourier.coordinateResidual
  exact abs_le.mpr ⟨by linarith [hf0 x], by linarith [hf1 x]⟩

/-- Boolean residual absolute first moment is exactly resampling influence,
including the endpoint biases. -/
theorem boolean_residual_abs_mean {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) (i : ι) :
    ProductMeasure.expectation p
      (fun x => |Fourier.coordinateResidual p (fun x => Influence.boolValue (f x)) i x|) =
      Influence.resamplingInfluence p f i := by
  rw [Influence.expectation_split_inside p i, Influence.resamplingInfluence_eq_fiber]
  congr 1
  funext z
  simp only [Fourier.coordinateResidual, Fourier.coordinateMean, Influence.update_insertBit]
  cases hf : f (ProductMeasure.insertBit i false z) <;>
    cases ht : f (ProductMeasure.insertBit i true z) <;>
    simp [Influence.boolValue, Influence.fiberResampling, FiberShift.mismatch,
      abs_of_nonneg hp0, abs_of_nonneg (sub_nonneg.mpr hp1),
      abs_of_nonpos (neg_nonpos.mpr hp0), abs_of_nonpos (sub_nonpos.mpr hp1)]

/-- The L(4/3) moment of a Boolean coordinate residual is at most its exact
resampling influence. -/
theorem boolean_residual_moment43_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) (i : ι) :
    BourgainDuality.moment43 (ProductMeasure.weight p)
      (Fourier.coordinateResidual p (fun x => Influence.boolValue (f x)) i) ≤
        Influence.resamplingInfluence p f i := by
  rw [← boolean_residual_abs_mean hp0 hp1 f i]
  apply ProductMeasure.expectation_mono hp0 hp1
  intro x
  apply Real.rpow_le_self_of_le_one (abs_nonneg _)
  · exact coordinateResidual_abs_le_one hp0 hp1 _
      (fun x => by cases f x <;> norm_num [Influence.boolValue])
      (fun x => by cases f x <;> norm_num [Influence.boolValue]) i x
  · norm_num

/-- The integrated coordinate-square moment is charged to the actual
resampling influence, with a dimension-free constant. -/
theorem coordinateSquare_boolean_moment43 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (k : ℕ) (i : ι) :
    ProductMeasure.expectation p (fun x =>
      (BourgainComponents.coordinateSquare
        (Finset.univ.filter fun S : Finset ι => S.card ≤ k)
        (fun S => Fourier.component p (fun x => Influence.boolValue (f x)) S x) i) ^ (2/3 : ℝ)) ≤
        (3 : ℝ)^(2*k) * Influence.resamplingInfluence p f i := by
  simp_rw [coordinateSquare_eq_residual]
  exact (squareFunction_moment43 hp0 hp1 _ k).trans
    (mul_le_mul_of_nonneg_left (boolean_residual_moment43_le hp0.le hp1.le f i)
      (by positivity))

/-- Summing the coordinate-square moment costs only total resampling influence. -/
theorem sum_coordinateSquare_boolean_moment43 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (k : ℕ) :
    (∑ i, ProductMeasure.expectation p (fun x =>
      (BourgainComponents.coordinateSquare
        (Finset.univ.filter fun S : Finset ι => S.card ≤ k)
        (fun S => Fourier.component p (fun x => Influence.boolValue (f x)) S x) i) ^ (2/3 : ℝ))) ≤
        (3 : ℝ)^(2*k) * Influence.totalInfluence p f := by
  rw [Influence.totalInfluence, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => coordinateSquare_boolean_moment43 hp0 hp1 f k i

/-- Boolean functions have fourth moment at most one, so the total low-degree
square function has the required uniform fourth-moment bound. -/
theorem squareFunction_boolean_fourth {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (k : ℕ) :
    ProductMeasure.expectation p
      (fun x => squareFunction p (fun x => Influence.boolValue (f x)) k x ^ 2) ≤
        (3 : ℝ)^(4*k) := by
  have h := squareFunction_fourth hp0 hp1 (fun x => Influence.boolValue (f x)) k
  have hm : ProductMeasure.expectation p (fun x => Influence.boolValue (f x)^4) ≤ 1 := by
    rw [← ProductMeasure.expectation_one (ι := ι) p]
    apply ProductMeasure.expectation_mono hp0.le hp1.le
    intro x
    cases f x <;> norm_num [Influence.boolValue]
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (3 : ℝ)^(4*k))])

/-- Finite-family expectation commutes with its sum. -/
theorem expectation_finset_sum {α : Type*} (A : Finset α) (p : ℝ)
    (F : α → (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => ∑ a ∈ A, F a x) =
      ∑ a ∈ A, ProductMeasure.expectation p (F a) := by
  unfold ProductMeasure.expectation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- Integrated low-degree coordinate-square mass is at most half the
resampling influence, with the exact spectral normalization. -/
theorem coordinateSquare_total_mean_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (k : ℕ) :
    ProductMeasure.expectation p (fun x =>
      ∑ i, BourgainComponents.coordinateSquare
        (Finset.univ.filter fun S : Finset ι => S.card ≤ k)
        (fun S => Fourier.component p (fun x => Influence.boolValue (f x)) S x) i) ≤
          Influence.totalInfluence p f / 2 := by
  simp_rw [BourgainComponents.sum_coordinateSquare]
  rw [expectation_finset_sum]
  simp_rw [ProductMeasure.expectation_const_mul, Fourier.component_sq_mean hp0 hp1]
  rw [Fourier.totalInfluence_spectral_finset hp0 hp1]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun S _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

end NarrowDNF.BourgainSquareFunction
