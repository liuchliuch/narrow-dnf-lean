import NarrowDNF.Fourier
import NarrowDNF.BourgainDuality
import Mathlib.Tactic.Positivity

/-!
# Signed noise contraction for Bourgain's square-function argument

These are actual finite fourth-moment contraction theorems, uniform in the
Bernoulli bias. They do not assume a hypercontractive inequality. The negative
noise parameter is `-1/3`; using this slightly weaker parameter avoids any
unproved sharp-constant assertion from the cited appendix.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.BourgainNoise

/-- One-coordinate signed noise, including negative noise parameters. -/
def coordinateNoise {ι : Type*} [DecidableEq ι] (p ρ : ℝ)
    (f : (ι → Bool) → ℝ) (i : ι) (x : ι → Bool) : ℝ :=
  Fourier.coordinateMean p f i x + ρ * Fourier.coordinateResidual p f i x

/-- Polynomial certificate for negative noise. The linear correction disappears
when `b` has mean zero. -/
theorem negative_noise_polynomial (a b : ℝ) :
    (a - b / 3) ^ 4 + (4 / 3 : ℝ) * a ^ 3 * b ≤
      (a + b) ^ 4 - 4 * a ^ 3 * b := by
  have h := sq_nonneg (a * b + (7 / 18 : ℝ) * b ^ 2)
  have h' := sq_nonneg (b ^ 2)
  nlinarith

/-- The matching elementary certificate for positive noise. -/
theorem positive_noise_polynomial (a b : ℝ) :
    (a + b / 3) ^ 4 - (4 / 3 : ℝ) * a ^ 3 * b ≤
      (a + b) ^ 4 - 4 * a ^ 3 * b := by
  have h := sq_nonneg (a * b + (13 / 36 : ℝ) * b ^ 2)
  have h' := sq_nonneg (b ^ 2)
  nlinarith

/-- Negative noise contracts the fourth moment on every finite probability
space, not only on the unbiased two-point space. -/
theorem finite_negative_fourth_contraction {α : Type*} [Fintype α]
    (w f : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1) :
    (∑ x, w x * ((∑ y, w y * f y) - (f x - ∑ y, w y * f y) / 3) ^ 4) ≤
      ∑ x, w x * f x ^ 4 := by
  let a := ∑ y, w y * f y
  have hzero : (∑ x, w x * (f x - a)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    simp [a]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (negative_noise_polynomial a (f x - a)) (hw x))
  simp only [add_sub_cancel, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib] at hsum
  have hlinear (c : ℝ) : (∑ x, w x * (c * a ^ 3 * (f x - a))) = 0 := by
    calc
      _ = c * a ^ 3 * ∑ x, w x * (f x - a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hzero, mul_zero]
  simp only [mul_sub, Finset.sum_sub_distrib] at hlinear
  rw [hlinear, hlinear] at hsum
  simpa only [add_zero, sub_zero] using hsum

/-- Positive noise contracts the fourth moment on every finite probability
space, proved independently of Jensen or interpolation. -/
theorem finite_positive_fourth_contraction {α : Type*} [Fintype α]
    (w f : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1) :
    (∑ x, w x * ((∑ y, w y * f y) + (f x - ∑ y, w y * f y) / 3) ^ 4) ≤
      ∑ x, w x * f x ^ 4 := by
  let a := ∑ y, w y * f y
  have hzero : (∑ x, w x * (f x - a)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    simp [a]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (positive_noise_polynomial a (f x - a)) (hw x))
  simp only [add_sub_cancel, mul_sub, Finset.sum_sub_distrib] at hsum
  have hlinear (c : ℝ) : (∑ x, w x * (c * a ^ 3 * (f x - a))) = 0 := by
    calc
      _ = c * a ^ 3 * ∑ x, w x * (f x - a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hzero, mul_zero]
  simp only [mul_sub, Finset.sum_sub_distrib] at hlinear
  rw [hlinear, hlinear] at hsum
  simpa only [sub_zero] using hsum

section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coordinate_negative_fourth_contraction {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → ℝ) (i : ι) :
    ProductMeasure.expectation p (fun x => coordinateNoise p (-1/3) f i x ^ 4) ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  rw [Influence.expectation_split_inside p i, Influence.expectation_split_inside p i]
  apply ProductMeasure.expectation_mono hp0 hp1
  intro z
  have h := finite_negative_fourth_contraction
    (ProductMeasure.bitWeight p) (fun b => f (ProductMeasure.insertBit i b z))
    (ProductMeasure.bitWeight_nonneg hp0 hp1) (by simp)
  simp only [Fintype.sum_bool, ProductMeasure.bitWeight_true,
    ProductMeasure.bitWeight_false] at h
  simp only [coordinateNoise, Fourier.coordinateMean, Fourier.coordinateResidual,
    Influence.update_insertBit]
  convert h using 1 <;> ring

theorem coordinate_positive_fourth_contraction {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → ℝ) (i : ι) :
    ProductMeasure.expectation p (fun x => coordinateNoise p (1/3) f i x ^ 4) ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  rw [Influence.expectation_split_inside p i, Influence.expectation_split_inside p i]
  apply ProductMeasure.expectation_mono hp0 hp1
  intro z
  have h := finite_positive_fourth_contraction
    (ProductMeasure.bitWeight p) (fun b => f (ProductMeasure.insertBit i b z))
    (ProductMeasure.bitWeight_nonneg hp0 hp1) (by simp)
  simp only [Fintype.sum_bool, ProductMeasure.bitWeight_true,
    ProductMeasure.bitWeight_false] at h
  simp only [coordinateNoise, Fourier.coordinateMean, Fourier.coordinateResidual,
    Influence.update_insertBit]
  convert h using 1 <;> ring

/-- A list of coordinate noises. No commutation or distinctness hypothesis is
needed for the contraction theorem. -/
def noiseList (p : ℝ) (ρ : ι → ℝ) : List ι → ((ι → Bool) → ℝ) → ((ι → Bool) → ℝ)
  | [], f => f
  | i :: L, f => coordinateNoise p (ρ i) (noiseList p ρ L f) i

/-- Tensorization of the signed-noise fourth-moment estimate, including
arbitrary repeated coordinates. -/
theorem noiseList_fourth_contraction {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : ι → ℝ) (hρ : ∀ i, ρ i = 1/3 ∨ ρ i = -1/3)
    (L : List ι) (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => noiseList p ρ L f x ^ 4) ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  induction L with
  | nil => exact le_rfl
  | cons i L ih =>
    simp only [noiseList]
    refine le_trans ?_ ih
    rcases hρ i with h | h <;> rw [h]
    · exact coordinate_positive_fourth_contraction hp0 hp1 _ i
    · exact coordinate_negative_fourth_contraction hp0 hp1 _ i

/-- The exact coordinate-noise multiplier on the biased Fourier transform. -/
theorem coefficient_coordinateNoise (p ρ : ℝ) (f : (ι → Bool) → ℝ)
    (i : ι) (s : ι → Bool) :
    Fourier.coefficient p (coordinateNoise p ρ f i) s =
      (if s i then ρ else 1) * Fourier.coefficient p f s := by
  unfold coordinateNoise Fourier.coefficient
  simp_rw [add_mul, mul_assoc]
  rw [ProductMeasure.expectation_add, ProductMeasure.expectation_const_mul,
    Fourier.coordinateMean_selfAdjoint]
  simp_rw [Fourier.coordinateMean_character]
  change ProductMeasure.expectation p
      (fun x => f x * (if s i then 0 else Fourier.character p s x)) +
      ρ * Fourier.coefficient p (Fourier.coordinateResidual p f i) s = _
  rw [Fourier.coefficient_coordinateResidual]
  cases s i <;> simp [Fourier.coefficient]

/-- Fourier multipliers of a finite sequence multiply. -/
theorem coefficient_noiseList (p : ℝ) (ρ : ι → ℝ) (L : List ι)
    (f : (ι → Bool) → ℝ) (s : ι → Bool) :
    Fourier.coefficient p (noiseList p ρ L f) s =
      (L.map (fun i => if s i then ρ i else 1)).prod * Fourier.coefficient p f s := by
  induction L with
  | nil => simp [noiseList]
  | cons i L ih =>
    simp only [noiseList, coefficient_coordinateNoise, ih, List.map_cons, List.prod_cons]
    ring

/-- Spectral signed noise with an independently selected multiplier per coordinate. -/
def tensorNoise (p : ℝ) (ρ : ι → ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ s : ι → Bool, (∏ i, if s i then ρ i else 1) *
    Fourier.coefficient p f s * Fourier.character p s x

/-- The spectral expression is the composition of the actual coordinate operators. -/
theorem tensorNoise_eq_noiseList {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ι → ℝ) (f : (ι → Bool) → ℝ) :
    tensorNoise p ρ f = noiseList p ρ Finset.univ.toList f := by
  funext x
  rw [← Fourier.expansion hp0 hp1 (noiseList p ρ Finset.univ.toList f) x]
  unfold tensorNoise
  apply Finset.sum_congr rfl
  intro s _
  rw [coefficient_noiseList]
  simp

/-- Full arbitrary-dimensional signed-noise L4 contraction. -/
theorem tensorNoise_fourth_contraction {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ι → ℝ) (hρ : ∀ i, ρ i = 1/3 ∨ ρ i = -1/3)
    (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => tensorNoise p ρ f x ^ 4) ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  rw [tensorNoise_eq_noiseList hp0 hp1]
  exact noiseList_fourth_contraction hp0.le hp1.le ρ hρ _ f

/-- Kernel formula for spectral noise. This gives a direct bridge to tensorized
finite kernel inequalities without any cross-type Fourier induction. -/
theorem tensorNoise_eq_productKernel (p : ℝ) (ρ : ι → ℝ)
    (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    tensorNoise p ρ f x = ∑ y : ι → Bool,
      (∏ i, ProductMeasure.bitWeight p (y i) *
        (1 + ρ i * Fourier.standardBit p (x i) * Fourier.standardBit p (y i))) * f y := by
  unfold tensorNoise Fourier.coefficient ProductMeasure.expectation
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ProductMeasure.weight p y * f y *
        ∑ s : ι → Bool, ∏ i, (if s i then ρ i else 1) *
          Fourier.bitBasis p (s i) (x i) * Fourier.bitBasis p (s i) (y i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [Finset.prod_mul_distrib, Fourier.character]
      ring
    _ = ProductMeasure.weight p y * f y *
        ∏ i, ∑ b : Bool, (if b then ρ i else 1) *
          Fourier.bitBasis p b (x i) * Fourier.bitBasis p b (y i) := by
      congr 1
      exact ProductMeasure.sum_prod_coordinates
        (fun i b => (if b then ρ i else 1) *
          Fourier.bitBasis p b (x i) * Fourier.bitBasis p b (y i))
    _ = _ := by
      simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
        Fourier.bitBasis, mul_one, ProductMeasure.weight,
        Finset.prod_mul_distrib]
      rw [mul_comm (∏ i, ProductMeasure.bitWeight p (y i)) (f y), mul_assoc]
      rw [mul_comm (f y)]
      congr 2
      apply Finset.prod_congr rfl
      intro i _
      ring

/-- The product kernel is symmetric, so spectral tensor noise is self-adjoint
for the biased inner product. The identity is purely algebraic. -/
theorem tensorNoise_selfAdjoint (p : ℝ) (ρ : ι → ℝ)
    (f g : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => tensorNoise p ρ f x * g x) =
      ProductMeasure.expectation p (fun x => f x * tensorNoise p ρ g x) := by
  have hinner (f g : (ι → Bool) → ℝ) :
      ProductMeasure.expectation p (fun x => tensorNoise p ρ f x * g x) =
        ∑ s : ι → Bool, (∏ i, if s i then ρ i else 1) *
          Fourier.coefficient p f s * Fourier.coefficient p g s := by
    unfold tensorNoise
    simp_rw [Finset.sum_mul]
    rw [Influence.expectation_sum]
    apply Finset.sum_congr rfl
    intro s _
    calc
      _ = ProductMeasure.expectation p (fun x =>
          ((∏ i, if s i then ρ i else 1) * Fourier.coefficient p f s) *
            (g x * Fourier.character p s x)) := by
        congr 1
        funext x
        ring
      _ = _ := ProductMeasure.expectation_const_mul _ _ _
  rw [hinner]
  have hcomm : ProductMeasure.expectation p (fun x => f x * tensorNoise p ρ g x) =
      ProductMeasure.expectation p (fun x => tensorNoise p ρ g x * f x) := by
    congr 1
    funext x
    ring
  rw [hcomm, hinner]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Signed tensor noise contracts the L(4/3) moment, by the proved finite
self-adjoint duality theorem. -/
theorem tensorNoise_moment43_contraction {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ι → ℝ) (hρ : ∀ i, ρ i = 1/3 ∨ ρ i = -1/3)
    (f : (ι → Bool) → ℝ) :
    BourgainDuality.moment43 (ProductMeasure.weight p) (tensorNoise p ρ f) ≤
      BourgainDuality.moment43 (ProductMeasure.weight p) f := by
  apply BourgainDuality.dual_fourth_contraction
    (ProductMeasure.weight p) (ProductMeasure.weight_nonneg hp0.le hp1.le)
    (tensorNoise p ρ) _ _ f
  · intro f g
    simpa only [ProductMeasure.expectation, mul_assoc] using
      tensorNoise_selfAdjoint p ρ f g
  · intro f
    exact tensorNoise_fourth_contraction hp0 hp1 ρ hρ f

/-- The exact Fourier multiplier of tensor noise, without requiring any
contraction or sign restriction on the coordinate parameters. -/
theorem coefficient_tensorNoise {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ι → ℝ) (f : (ι → Bool) → ℝ) (s : ι → Bool) :
    Fourier.coefficient p (tensorNoise p ρ f) s =
      (∏ i, if s i then ρ i else 1) * Fourier.coefficient p f s := by
  rw [tensorNoise_eq_noiseList hp0 hp1, coefficient_noiseList]
  simp

/-- Exact second moment of tensor noise. -/
theorem tensorNoise_secondMoment {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ι → ℝ) (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => tensorNoise p ρ f x ^ 2) =
      ∑ s : ι → Bool, ((∏ i, if s i then ρ i else 1) * Fourier.coefficient p f s)^2 := by
  rw [Fourier.parseval hp0 hp1]
  simp_rw [coefficient_tensorNoise hp0 hp1]

end Cube
end NarrowDNF.BourgainNoise
