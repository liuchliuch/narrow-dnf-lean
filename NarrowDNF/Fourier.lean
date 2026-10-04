import NarrowDNF.Influence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite biased Fourier expansion

A basis index is a Boolean support mask. Its true coordinates are exactly the
usual subset index. All expectations use Bernoulli product weights, and the
normalization of influence is independent resampling rather than bit flipping.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Fourier

/-- Centered normalized Bernoulli bit. -/
def standardBit (p : ℝ) (b : Bool) : ℝ :=
  (if b then 1-p else -p) / Real.sqrt (p * (1-p))

/-- The two one-coordinate orthonormal functions: constant and centered bit. -/
def bitBasis (p : ℝ) (s b : Bool) : ℝ := if s then standardBit p b else 1

theorem sqrt_bias_ne_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Real.sqrt (p * (1-p)) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (mul_pos hp0 (sub_pos.mpr hp1)))

theorem bit_orthogonality {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (s t : Bool) :
    (1-p) * (bitBasis p s false * bitBasis p t false) +
      p * (bitBasis p s true * bitBasis p t true) = if s = t then 1 else 0 := by
  have hs := sqrt_bias_ne_zero hp0 hp1
  have hs2 := Real.sq_sqrt (le_of_lt (mul_pos hp0 (sub_pos.mpr hp1)))
  cases s <;> cases t <;> simp [bitBasis, standardBit]
  all_goals field_simp
  all_goals nlinarith

/-- One-bit reproducing kernel, with its probability mass already included. -/
theorem bit_kernel {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (a b : Bool) :
    ProductMeasure.bitWeight p b *
      (bitBasis p false a * bitBasis p false b +
        bitBasis p true a * bitBasis p true b) = if a = b then 1 else 0 := by
  have hs := sqrt_bias_ne_zero hp0 hp1
  have hs2 := Real.sq_sqrt (le_of_lt (mul_pos hp0 (sub_pos.mpr hp1)))
  cases a <;> cases b <;> simp [bitBasis, standardBit, ProductMeasure.bitWeight]
  all_goals field_simp
  all_goals simp [hs2] <;> ring_nf <;> simp

section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Tensor basis indexed by the coordinates selected by a Boolean support mask. -/
def character (p : ℝ) (s x : ι → Bool) : ℝ := ∏ i, bitBasis p (s i) (x i)

/-- Fourier coefficient in the real biased orthonormal basis. -/
def coefficient (p : ℝ) (f : (ι → Bool) → ℝ) (s : ι → Bool) : ℝ :=
  ProductMeasure.expectation p (fun x => f x * character p s x)

/-- Spectral degree, equivalently the cardinality of the support subset. -/
def degree (s : ι → Bool) : ℕ := (Finset.univ.filter fun i => s i = true).card

/-- Orthonormality for the biased product measure. -/
theorem orthogonality {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (s t : ι → Bool) :
    ProductMeasure.expectation p (fun x => character p s x * character p t x) =
      if s = t then 1 else 0 := by
  unfold character
  simp_rw [← Finset.prod_mul_distrib]
  rw [ProductMeasure.expectation_prod p (fun i b => bitBasis p (s i) b * bitBasis p (t i) b)]
  simp_rw [bit_orthogonality hp0 hp1]
  rw [Fintype.prod_boole]
  simp only [funext_iff]

/-- Tensorized reproducing kernel. -/
theorem kernel {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x y : ι → Bool) :
    ProductMeasure.weight p y *
      (∑ s : ι → Bool, character p s x * character p s y) =
      if x = y then 1 else 0 := by
  unfold character
  simp_rw [← Finset.prod_mul_distrib]
  rw [ProductMeasure.sum_prod_coordinates (fun i b => bitBasis p b (x i) * bitBasis p b (y i))]
  unfold ProductMeasure.weight
  rw [← Finset.prod_mul_distrib]
  simp_rw [Fintype.sum_bool]
  have hbit (i : ι) : ProductMeasure.bitWeight p (y i) *
      (bitBasis p true (x i) * bitBasis p true (y i) +
        bitBasis p false (x i) * bitBasis p false (y i)) =
      if x i = y i then 1 else 0 := by
    rw [add_comm]
    exact bit_kernel hp0 hp1 (x i) (y i)
  simp_rw [hbit]
  rw [Fintype.prod_boole]
  simp only [funext_iff]


/-- Pointwise reconstruction of every real-valued function on the finite cube. -/
theorem expansion {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    (∑ s : ι → Bool, coefficient p f s * character p s x) = f x := by
  unfold coefficient ProductMeasure.expectation
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y : ι → Bool, f y * (ProductMeasure.weight p y *
        ∑ s : ι → Bool, character p s x * character p s y) := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = ∑ y : ι → Bool, f y * (if x = y then 1 else 0) := by
      simp_rw [kernel hp0 hp1]
    _ = f x := by simp

/-- The finite inner-product Parseval identity. -/
theorem inner_parseval {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f g : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => f x * g x) =
      ∑ s : ι → Bool, coefficient p f s * coefficient p g s := by
  calc
    _ = ProductMeasure.expectation p (fun x =>
        ∑ s : ι → Bool, coefficient p g s * (f x * character p s x)) := by
      congr 1
      funext x
      calc
        f x * g x = f x * (∑ s : ι → Bool, coefficient p g s * character p s x) := by
          rw [expansion hp0 hp1]
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = ∑ s : ι → Bool, ProductMeasure.expectation p
        (fun x => coefficient p g s * (f x * character p s x)) :=
      Influence.expectation_sum p _
    _ = ∑ s : ι → Bool, coefficient p f s * coefficient p g s := by
      simp_rw [ProductMeasure.expectation_const_mul]
      apply Finset.sum_congr rfl
      intro s _
      exact mul_comm _ _

/-- Parseval: squared L2 norm equals total squared Fourier mass. -/
theorem parseval {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => f x ^ 2) =
      ∑ s : ι → Bool, coefficient p f s ^ 2 := by
  simpa only [pow_two] using inner_parseval hp0 hp1 f f


/-- Conditional averaging in one input coordinate. -/
def coordinateMean (p : ℝ) (f : (ι → Bool) → ℝ) (i : ι) (x : ι → Bool) : ℝ :=
  (1-p) * f (Function.update x i false) + p * f (Function.update x i true)

/-- The component removed by conditional averaging in a coordinate. -/
def coordinateResidual (p : ℝ) (f : (ι → Bool) → ℝ) (i : ι) (x : ι → Bool) : ℝ :=
  f x - coordinateMean p f i x

theorem character_split (p : ℝ) (s x : ι → Bool) (i : ι) :
    character p s x = bitBasis p (s i) (x i) *
      ∏ j : {j // j ≠ i}, bitBasis p (s j) (x j) :=
  Fintype.prod_eq_mul_prod_subtype_ne (fun j => bitBasis p (s j) (x j)) i

theorem character_update (p : ℝ) (s x : ι → Bool) (i : ι) (b : Bool) :
    character p s (Function.update x i b) = bitBasis p (s i) b *
      ∏ j : {j // j ≠ i}, bitBasis p (s j) (x j) := by
  rw [character_split p s _ i]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [Function.update_of_ne j.property]

/-- Conditional averaging kills exactly the basis functions using that coordinate. -/
theorem coordinateMean_character (p : ℝ) (s x : ι → Bool) (i : ι) :
    coordinateMean p (character p s) i x = if s i then 0 else character p s x := by
  unfold coordinateMean
  rw [character_update, character_update]
  rw [character_split p s x i]
  cases s i <;> simp [bitBasis, standardBit, div_eq_mul_inv] <;> ring

theorem expectation_sub (p : ℝ) (f g : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => f x - g x) =
      ProductMeasure.expectation p f - ProductMeasure.expectation p g := by
  simp [ProductMeasure.expectation, mul_sub, Finset.sum_sub_distrib]

/-- Conditional expectation is self-adjoint for the finite weighted inner product. -/
theorem coordinateMean_selfAdjoint (p : ℝ) (f g : (ι → Bool) → ℝ) (i : ι) :
    ProductMeasure.expectation p (fun x => coordinateMean p f i x * g x) =
      ProductMeasure.expectation p (fun x => f x * coordinateMean p g i x) := by
  rw [Influence.expectation_split_inside p i,
    Influence.expectation_split_inside p i]
  congr 1
  funext z
  simp only [coordinateMean, Influence.update_insertBit]
  ring

/-- The Fourier multiplier of the coordinate residual is the coordinate's support bit. -/
theorem coefficient_coordinateResidual (p : ℝ) (f : (ι → Bool) → ℝ)
    (i : ι) (s : ι → Bool) :
    coefficient p (coordinateResidual p f i) s = if s i then coefficient p f s else 0 := by
  unfold coefficient coordinateResidual
  simp_rw [sub_mul]
  rw [expectation_sub, coordinateMean_selfAdjoint]
  simp_rw [coordinateMean_character]
  cases s i <;> simp

/-- Squared L2 norm of the coordinate residual is averaged conditional variance. -/
theorem residual_sq_eq_coordinateVariance (p : ℝ) (f : (ι → Bool) → ℝ) (i : ι) :
    ProductMeasure.expectation p (fun x => coordinateResidual p f i x ^ 2) =
      Influence.coordinateVariance p f i := by
  rw [Influence.expectation_split_inside p i]
  unfold Influence.coordinateVariance
  congr 1
  funext z
  simp only [coordinateResidual, coordinateMean, Influence.update_insertBit,
    Influence.fiberVariance, Influence.fiberMean]

/-- Conditional variance equals the squared Fourier mass using the coordinate. -/
theorem coordinateVariance_spectral {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (i : ι) :
    Influence.coordinateVariance p f i =
      ∑ s : ι → Bool, if s i then coefficient p f s ^ 2 else 0 := by
  rw [← residual_sq_eq_coordinateVariance, parseval hp0 hp1]
  simp_rw [coefficient_coordinateResidual]
  apply Finset.sum_congr rfl
  intro s _
  cases s i <;> simp

/-- Exact per-coordinate influence normalization in the biased Fourier basis. -/
theorem resamplingInfluence_spectral {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (i : ι) :
    Influence.resamplingInfluence p f i =
      2 * ∑ s : ι → Bool, if s i then coefficient p (fun x => Influence.boolValue (f x)) s ^ 2 else 0 := by
  rw [Influence.resamplingInfluence_eq_twice_coordinateVariance,
    coordinateVariance_spectral hp0 hp1]

omit [DecidableEq ι] in
/-- Sum of the support indicators is spectral degree. -/
theorem sum_support (s : ι → Bool) (a : ℝ) :
    (∑ i, if s i then a else 0) = (degree s : ℝ) * a := by
  classical
  simp [degree, ← Finset.sum_filter]

/-- The paper's Fourier identity, with the precise factor of two from resampling. -/
theorem totalInfluence_spectral {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    Influence.totalInfluence p f = 2 *
      ∑ s : ι → Bool, (degree s : ℝ) *
        coefficient p (fun x => Influence.boolValue (f x)) s ^ 2 := by
  unfold Influence.totalInfluence
  simp_rw [resamplingInfluence_spectral hp0 hp1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact sum_support s _


/-- Explicit equivalence between support masks and the paper's subset indices. -/
def maskEquivFinset : (ι → Bool) ≃ Finset ι where
  toFun s := Finset.univ.filter fun i => s i = true
  invFun S i := decide (i ∈ S)
  left_inv s := by
    funext i
    simp
  right_inv S := by
    ext i
    simp

/-- The same Fourier coefficient indexed by a finite subset. -/
def setCoefficient (p : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  coefficient p f (maskEquivFinset.symm S)

/-- The same basis function indexed by a finite subset. -/
def setCharacter (p : ℝ) (S : Finset ι) (x : ι → Bool) : ℝ :=
  character p (maskEquivFinset.symm S) x

/-- The subset-indexed form of the exact resampling spectral identity. -/
theorem totalInfluence_spectral_finset {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    Influence.totalInfluence p f = 2 *
      ∑ S : Finset ι, (S.card : ℝ) *
        setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 := by
  rw [totalInfluence_spectral hp0 hp1]
  congr 1
  apply Fintype.sum_equiv maskEquivFinset
  intro s
  simp only [setCoefficient, Equiv.symm_apply_apply]
  rfl

/-- Exact first absolute moment of the normalized biased bit. -/
theorem standardBit_abs_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (1-p) * |standardBit p false| + p * |standardBit p true| =
      2 * Real.sqrt (p * (1-p)) := by
  have hspos := Real.sqrt_pos.mpr (mul_pos hp0 (sub_pos.mpr hp1))
  have hs := ne_of_gt hspos
  have hs2 := Real.sq_sqrt (le_of_lt (mul_pos hp0 (sub_pos.mpr hp1)))
  simp only [standardBit, Bool.false_eq_true, ↓reduceIte, abs_div, abs_neg,
    abs_of_pos hp0, abs_of_pos (sub_pos.mpr hp1), abs_of_pos hspos]
  field_simp
  nlinarith

/-- Absolute L1 norm of a biased basis function; this is where the factor
`2 ^ |S|` absent from the paper's quoted bound arises. -/
theorem character_abs_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (s : ι → Bool) :
    ProductMeasure.expectation p (fun x => |character p s x|) =
      (2 * Real.sqrt (p * (1-p))) ^ degree s := by
  unfold character
  simp_rw [Finset.abs_prod]
  rw [ProductMeasure.expectation_prod p (fun i b => |bitBasis p (s i) b|)]
  have hbit (i : ι) : (1-p) * |bitBasis p (s i) false| +
      p * |bitBasis p (s i) true| =
        if s i then 2 * Real.sqrt (p * (1-p)) else 1 := by
    cases hs : s i
    · simp [bitBasis]
    · exact standardBit_abs_mean hp0 hp1
  simp_rw [hbit]
  simp [degree, ← Finset.prod_filter]

/-- A safe coefficient bound for every Boolean function. The product-measure
L1 estimate is stronger than `2^|S| * p^(|S|/2)` in the low-bias range. -/
theorem coefficient_bool_abs_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (s : ι → Bool) :
    |coefficient p (fun x => Influence.boolValue (f x)) s| ≤
      (2 * Real.sqrt (p * (1-p))) ^ degree s := by
  rw [← character_abs_mean hp0 hp1]
  unfold coefficient ProductMeasure.expectation
  calc
    _ ≤ ∑ x : ι → Bool,
        |ProductMeasure.weight p x * (Influence.boolValue (f x) * character p s x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (ProductMeasure.weight_nonneg hp0.le hp1.le x)]
      apply mul_le_mul_of_nonneg_left _ (ProductMeasure.weight_nonneg hp0.le hp1.le x)
      cases f x <;> simp [Influence.boolValue]


omit [DecidableEq ι] in
/-- Degree zero means the constant basis function. -/
theorem degree_eq_zero_iff (s : ι → Bool) : degree s = 0 ↔ s = fun _ => false := by
  rw [degree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    exact Bool.eq_false_iff.mpr (h (Finset.mem_univ i))
  · intro h
    subst s
    simp

/-- The constant Fourier coefficient is the mean. -/
@[simp] theorem coefficient_zeroMask (p : ℝ) (f : (ι → Bool) → ℝ) :
    coefficient p f (fun _ => false) = ProductMeasure.expectation p f := by
  simp [coefficient, character, bitBasis]

/-- Variance is the nonconstant squared Fourier mass. -/
theorem variance_spectral {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) :
    Influence.variance p f = ∑ s ∈ Finset.univ.erase (fun _ : ι => false), coefficient p f s ^ 2 := by
  rw [Influence.variance_eq_secondMoment, parseval hp0 hp1]
  have h := Finset.sum_erase_add (Finset.univ : Finset (ι → Bool))
    (fun s => coefficient p f s ^ 2) (Finset.mem_univ (fun _ : ι => false))
  dsimp only at h
  rw [coefficient_zeroMask] at h
  linarith

/-- Every nonconstant degree is at least one, giving the product Poincare estimate. -/
theorem variance_le_spectralEnergy {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) :
    Influence.variance p f ≤ ∑ s : ι → Bool, (degree s : ℝ) * coefficient p f s ^ 2 := by
  rw [variance_spectral hp0 hp1]
  calc
    _ ≤ ∑ s ∈ Finset.univ.erase (fun _ : ι => false),
        (degree s : ℝ) * coefficient p f s ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      have hne : s ≠ (fun _ : ι => false) := (Finset.mem_erase.mp hs).1
      have hd : 1 ≤ degree s := Nat.one_le_iff_ne_zero.mpr (fun h => hne ((degree_eq_zero_iff s).mp h))
      have hdreal : (1 : ℝ) ≤ degree s := by exact_mod_cast hd
      nlinarith [sq_nonneg (coefficient p f s)]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro s _ _
      exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- Product Poincare in the paper's resampling convention. -/
theorem poincare {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    Influence.variance p (fun x => Influence.boolValue (f x)) ≤
      Influence.totalInfluence p f / 2 := by
  rw [totalInfluence_spectral hp0 hp1]
  have h := variance_le_spectralEnergy hp0 hp1 (fun x => Influence.boolValue (f x))
  linarith

/-- High-degree squared Fourier mass bound with the integer cutoff sharpened
from `k` to `k + 1`. -/
theorem highDegree_mass_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (k : ℕ) :
    (∑ s ∈ Finset.univ.filter (fun s : ι → Bool => k < degree s),
      coefficient p (fun x => Influence.boolValue (f x)) s ^ 2) ≤
        Influence.totalInfluence p f / (2 * (k+1 : ℕ)) := by
  let a := fun s : ι → Bool => coefficient p (fun x => Influence.boolValue (f x)) s ^ 2
  have h : ((k+1 : ℕ) : ℝ) * (∑ s ∈ Finset.univ.filter (fun s => k < degree s), a s) ≤
      ∑ s : ι → Bool, (degree s : ℝ) * a s := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ s ∈ Finset.univ.filter (fun s => k < degree s), (degree s : ℝ) * a s := by
        apply Finset.sum_le_sum
        intro s hs
        have hd : k+1 ≤ degree s := (Finset.mem_filter.mp hs).2
        have hdreal : ((k+1 : ℕ) : ℝ) ≤ degree s := by exact_mod_cast hd
        exact mul_le_mul_of_nonneg_right hdreal (sq_nonneg _)
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro s _ _
        exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  rw [totalInfluence_spectral hp0 hp1]
  have hk : (0 : ℝ) < (k+1 : ℕ) := by positivity
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hk)).mpr
  dsimp [a] at h
  nlinarith

/-- With full-support Bernoulli weights, zero variance forces pointwise constancy. -/
theorem eq_mean_of_variance_le_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (hf : Influence.variance p f ≤ 0) (x : ι → Bool) :
    f x = ProductMeasure.expectation p f := by
  have hnon (y : ι → Bool) : 0 ≤ ProductMeasure.weight p y *
      (f y - ProductMeasure.expectation p f) ^ 2 :=
    mul_nonneg (ProductMeasure.weight_nonneg hp0.le hp1.le y) (sq_nonneg _)
  have hle := Finset.single_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (ι → Bool))) => hnon y)
    (Finset.mem_univ x)
  have hz : ProductMeasure.weight p x * (f x - ProductMeasure.expectation p f) ^ 2 = 0 := by
    apply le_antisymm _ (hnon x)
    exact hle.trans hf
  have hs : (f x - ProductMeasure.expectation p f) ^ 2 = 0 :=
    (mul_eq_zero.mp hz).resolve_left (ne_of_gt (ProductMeasure.weight_pos hp0 hp1 x))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)

/-- Zero resampling influence means a Boolean function is genuinely constant,
not merely almost surely constant, because every cube point has positive mass. -/
theorem constant_of_totalInfluence_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (hf : Influence.totalInfluence p f = 0)
    (x y : ι → Bool) : f x = f y := by
  have hv : Influence.variance p (fun z => Influence.boolValue (f z)) ≤ 0 := by
    have h := poincare hp0 hp1 f
    simpa [hf] using h
  have hx := eq_mean_of_variance_le_zero hp0 hp1 (fun z => Influence.boolValue (f z)) hv x
  have hy := eq_mean_of_variance_le_zero hp0 hp1 (fun z => Influence.boolValue (f z)) hv y
  have hxy : Influence.boolValue (f x) = Influence.boolValue (f y) := hx.trans hy.symm
  exact Influence.boolValue_injective hxy


@[simp] theorem degree_maskEquivFinset_symm (S : Finset ι) :
    degree (maskEquivFinset.symm S) = S.card :=
  congrArg Finset.card (maskEquivFinset.apply_symm_apply S)

/-- The subset-indexed character is the usual product of centered normalized bits. -/
theorem setCharacter_eq_prod (p : ℝ) (S : Finset ι) (x : ι → Bool) :
    setCharacter p S x = ∏ i ∈ S, standardBit p (x i) := by
  simp [setCharacter, character, maskEquivFinset, bitBasis]

/-- Exact safe coefficient estimate with the paper's subset indices. -/
theorem setCoefficient_bool_abs_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (S : Finset ι) :
    |setCoefficient p (fun x => Influence.boolValue (f x)) S| ≤
      (2 * Real.sqrt (p * (1-p))) ^ S.card := by
  simpa only [setCoefficient, degree_maskEquivFinset_symm] using
    coefficient_bool_abs_le hp0 hp1 f (maskEquivFinset.symm S)

/-- A simpler safe coefficient bound retaining the necessary factor `2 ^ |S|`. -/
theorem setCoefficient_bool_abs_le_two_sqrt {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (S : Finset ι) :
    |setCoefficient p (fun x => Influence.boolValue (f x)) S| ≤
      (2 * Real.sqrt p) ^ S.card := by
  apply (setCoefficient_bool_abs_le hp0 hp1 f S).trans
  apply pow_le_pow_left₀ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) _ S.card
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg p]

/-- Subset-indexed high-degree truncation bound. -/
theorem highDegree_mass_le_finset {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (k : ℕ) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset ι => k < S.card),
      setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2) ≤
        Influence.totalInfluence p f / (2 * (k+1 : ℕ)) := by
  have heq : (∑ s ∈ Finset.univ.filter (fun s : ι → Bool => k < degree s),
      coefficient p (fun x => Influence.boolValue (f x)) s ^ 2) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => k < S.card),
        setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 := by
    simp only [Finset.sum_filter]
    apply Fintype.sum_equiv maskEquivFinset
    intro s
    simp only [setCoefficient, Equiv.symm_apply_apply]
    rfl
  rw [← heq]
  exact highDegree_mass_le hp0 hp1 f k


/-- Generalized Walsh component in the subset-indexed Fourier decomposition. -/
def component (p : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) (x : ι → Bool) : ℝ :=
  setCoefficient p f S * setCharacter p S x

/-- A subset-indexed basis function depends only on its indexing coordinates. -/
theorem setCharacter_locality (p : ℝ) (S : Finset ι) (x y : ι → Bool)
    (hxy : ∀ i ∈ S, x i = y i) : setCharacter p S x = setCharacter p S y := by
  rw [setCharacter_eq_prod, setCharacter_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hxy i hi]

/-- Each generalized Walsh component is local to its indexing subset. -/
theorem component_locality (p : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι)
    (x y : ι → Bool) (hxy : ∀ i ∈ S, x i = y i) :
    component p f S x = component p f S y := by
  unfold component
  rw [setCharacter_locality p S x y hxy]

/-- Every subset-indexed biased basis function has squared L2 norm one. -/
theorem setCharacter_sq_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S : Finset ι) :
    ProductMeasure.expectation p (fun x => setCharacter p S x ^ 2) = 1 := by
  simpa only [setCharacter, pow_two, if_pos rfl] using
    orthogonality hp0 hp1 (maskEquivFinset.symm S) (maskEquivFinset.symm S)

/-- The squared L2 mass of a generalized Walsh component is its squared coefficient. -/
theorem component_sq_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (S : Finset ι) :
    ProductMeasure.expectation p (fun x => component p f S x ^ 2) =
      setCoefficient p f S ^ 2 := by
  simp only [component, mul_pow]
  rw [ProductMeasure.expectation_const_mul, setCharacter_sq_mean hp0 hp1, mul_one]

/-- Subset-indexed Parseval identity. -/
theorem parseval_finset {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => f x ^ 2) =
      ∑ S : Finset ι, setCoefficient p f S ^ 2 := by
  rw [parseval hp0 hp1]
  apply Fintype.sum_equiv maskEquivFinset
  intro s
  simp only [setCoefficient, Equiv.symm_apply_apply]

/-- Total squared coefficient mass of a Boolean function is at most one. -/
theorem boolean_energy_le_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    (∑ S : Finset ι, setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2) ≤ 1 := by
  rw [← parseval_finset hp0 hp1]
  calc
    _ ≤ ProductMeasure.expectation (ι := ι) p (fun _ => 1) := by
      apply ProductMeasure.expectation_mono hp0.le hp1.le
      intro x
      cases f x <;> norm_num [Influence.boolValue]
    _ = 1 := ProductMeasure.expectation_one p

/-- Total generalized Walsh component energy of a Boolean function is at most one. -/
theorem boolean_component_energy_le_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    (∑ S : Finset ι, ProductMeasure.expectation p
      (fun x => component p (fun y => Influence.boolValue (f y)) S x ^ 2)) ≤ 1 := by
  simp_rw [component_sq_mean hp0 hp1]
  exact boolean_energy_le_one hp0 hp1 f

end Cube
end NarrowDNF.Fourier






