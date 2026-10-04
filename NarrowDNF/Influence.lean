import NarrowDNF.FiberShift
import NarrowDNF.ProductMeasure
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite Bernoulli variance and resampling influence

The one-coordinate identities in this file use the paper's resampling
normalization: a pivotal Boolean fiber has influence `2 * p * (1 - p)`.
The endpoints `p = 0` and `p = 1` are included in the algebraic identities.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Influence

/-- The numerical encoding of a Boolean output. -/
def boolValue (b : Bool) : ℝ := if b then 1 else 0

/-- Mean of a two-point real-valued random variable. -/
def fiberMean (p a b : ℝ) : ℝ := (1 - p) * a + p * b

/-- Variance on a Bernoulli fiber, defined as the mean squared deviation. -/
def fiberVariance (p a b : ℝ) : ℝ :=
  (1 - p) * (a - fiberMean p a b) ^ 2 + p * (b - fiberMean p a b) ^ 2

/-- Exact Bernoulli variance, valid even for real endpoint values. -/
theorem fiberVariance_eq (p a b : ℝ) :
    fiberVariance p a b = p * (1 - p) * (b - a) ^ 2 := by
  unfold fiberVariance fiberMean
  ring

/-- Squared endpoint difference of Boolean values is their disagreement indicator. -/
theorem boolValue_sub_sq (a b : Bool) :
    (boolValue b - boolValue a) ^ 2 = FiberShift.mismatch a b := by
  cases a <;> cases b <;> norm_num [boolValue, FiberShift.mismatch]

/-- A Boolean fiber has positive conditional variance exactly when it is pivotal,
provided the Bernoulli bias is nondegenerate. -/
theorem bool_fiberVariance_eq (p : ℝ) (a b : Bool) :
    fiberVariance p (boolValue a) (boolValue b) =
      p * (1 - p) * FiberShift.mismatch a b := by
  rw [fiberVariance_eq, boolValue_sub_sq]

/-- Expected disagreement when both the input bit and its independent replacement
are sampled from the same Bernoulli distribution. -/
def fiberResampling (p : ℝ) (a b : Bool) : ℝ :=
  (1 - p) * ((1 - p) * FiberShift.mismatch a a + p * FiberShift.mismatch a b) +
    p * ((1 - p) * FiberShift.mismatch b a + p * FiberShift.mismatch b b)

theorem fiberResampling_eq (p : ℝ) (a b : Bool) :
    fiberResampling p a b = 2 * p * (1 - p) * FiberShift.mismatch a b := by
  cases a <;> cases b <;> simp [fiberResampling, FiberShift.mismatch] <;> ring

/-- The factor of two in the paper's influence convention. -/
theorem fiberResampling_eq_twice_variance (p : ℝ) (a b : Bool) :
    fiberResampling p a b = 2 * fiberVariance p (boolValue a) (boolValue b) := by
  rw [fiberResampling_eq, bool_fiberVariance_eq]
  ring


/-- The square of a Boolean numerical value is itself. -/
@[simp] theorem boolValue_sq (b : Bool) : boolValue b ^ 2 = boolValue b := by
  cases b <;> norm_num [boolValue]

theorem boolValue_injective : Function.Injective boolValue := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolValue]

section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Variance as a finite expectation of squared deviations. -/
def variance (p : ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  ProductMeasure.expectation p
    (fun x => (F x - ProductMeasure.expectation p F) ^ 2)

theorem variance_eq_secondMoment (p : ℝ) (F : (ι → Bool) → ℝ) :
    variance p F = ProductMeasure.expectation p (fun x => F x ^ 2) -
      ProductMeasure.expectation p F ^ 2 := by
  unfold variance
  calc
    _ = ProductMeasure.expectation p (fun x => F x ^ 2 +
        (-2 * ProductMeasure.expectation p F) * F x +
        ProductMeasure.expectation p F ^ 2) := by
          congr 1
          funext x
          ring
    _ = _ := by
      rw [ProductMeasure.expectation_add, ProductMeasure.expectation_add,
        ProductMeasure.expectation_const_mul, ProductMeasure.expectation_const]
      ring

/-- The Bernoulli output variance identity, for a Boolean function on any finite cube. -/
theorem variance_bool_eq (p : ℝ) (f : (ι → Bool) → Bool) :
    variance p (fun x => boolValue (f x)) =
      ProductMeasure.expectation p (fun x => boolValue (f x)) *
        (1 - ProductMeasure.expectation p (fun x => boolValue (f x))) := by
  rw [variance_eq_secondMoment]
  simp_rw [boolValue_sq]
  ring

omit [Fintype ι] in
/-- Replacing an inserted coordinate keeps the complementary input fixed. -/
theorem update_insertBit (i : ι) (b c : Bool) (z : {j // j ≠ i} → Bool) :
    Function.update (ProductMeasure.insertBit i b z) i c =
      ProductMeasure.insertBit i c z := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne h] using
      (ProductMeasure.insertBit_away i b z ⟨j,h⟩).trans
        (ProductMeasure.insertBit_away i c z ⟨j,h⟩).symm

/-- Disintegration with the two fiber contributions inside one expectation. -/
theorem expectation_split_inside (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p F = ProductMeasure.expectation p (fun z =>
      (1-p) * F (ProductMeasure.insertBit i false z) +
        p * F (ProductMeasure.insertBit i true z)) := by
  rw [ProductMeasure.expectation_add, ProductMeasure.expectation_const_mul,
    ProductMeasure.expectation_const_mul]
  exact ProductMeasure.expectation_split p i F

/-- Probability that a coordinate fiber is pivotal; the expectation is over
all the other coordinates. -/
def pivotalProbability (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ :=
  ProductMeasure.expectation p (fun z =>
    FiberShift.mismatch (f (ProductMeasure.insertBit i false z))
      (f (ProductMeasure.insertBit i true z)))

/-- Resampling influence: sample the original cube point and independently
replace the chosen coordinate by a fresh Bernoulli bit. -/
def resamplingInfluence (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ :=
  ProductMeasure.expectation p (fun x =>
    (1-p) * FiberShift.mismatch (f x) (f (Function.update x i false)) +
      p * FiberShift.mismatch (f x) (f (Function.update x i true)))

theorem resamplingInfluence_eq_fiber (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    resamplingInfluence p f i = ProductMeasure.expectation p (fun z =>
      fiberResampling p (f (ProductMeasure.insertBit i false z))
        (f (ProductMeasure.insertBit i true z))) := by
  unfold resamplingInfluence
  rw [expectation_split_inside p i]
  simp only [update_insertBit, fiberResampling]

/-- Coordinate influence in the resampling convention is `2p(1-p)` times
the probability of a pivotal coordinate fiber. -/
theorem resamplingInfluence_eq (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    resamplingInfluence p f i = 2 * p * (1-p) * pivotalProbability p f i := by
  rw [resamplingInfluence_eq_fiber]
  simp_rw [fiberResampling_eq]
  exact ProductMeasure.expectation_const_mul p (2 * p * (1-p)) _

/-- Averaged conditional variance in one coordinate. -/
def coordinateVariance (p : ℝ) (F : (ι → Bool) → ℝ) (i : ι) : ℝ :=
  ProductMeasure.expectation p (fun z =>
    fiberVariance p (F (ProductMeasure.insertBit i false z))
      (F (ProductMeasure.insertBit i true z)))

theorem resamplingInfluence_eq_twice_coordinateVariance
    (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    resamplingInfluence p f i = 2 * coordinateVariance p (fun x => boolValue (f x)) i := by
  rw [resamplingInfluence_eq_fiber]
  simp_rw [fiberResampling_eq_twice_variance]
  exact ProductMeasure.expectation_const_mul p 2 _

/-- Pointwise bit-flip sensitivity, expressed as a real-valued finite count. -/
def sensitivity (f : (ι → Bool) → Bool) (x : ι → Bool) : ℝ :=
  ∑ i, FiberShift.mismatch (f x) (f (Function.update x i (!(x i))))

/-- Total influence in the paper's resampling normalization. -/
def totalInfluence (p : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  ∑ i, resamplingInfluence p f i

theorem flipExpectation_eq_pivotal (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    ProductMeasure.expectation p
      (fun x => FiberShift.mismatch (f x) (f (Function.update x i (!(x i))))) =
        pivotalProbability p f i := by
  rw [expectation_split_inside p i]
  unfold pivotalProbability
  congr 1
  funext z
  simp only [ProductMeasure.insertBit_at, Bool.not_false, Bool.not_true, update_insertBit]
  cases f (ProductMeasure.insertBit i false z) <;>
    cases f (ProductMeasure.insertBit i true z) <;> simp [FiberShift.mismatch]

theorem expectation_sum {κ : Type*} [Fintype κ] (p : ℝ)
    (F : κ → (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => ∑ i, F i x) =
      ∑ i, ProductMeasure.expectation p (F i) := by
  simp only [ProductMeasure.expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- Equation (2), first equality: valid for every Boolean function, with no
monotonicity assumption, including the endpoint biases. -/
theorem totalInfluence_eq_sensitivity (p : ℝ) (f : (ι → Bool) → Bool) :
    totalInfluence p f = 2 * p * (1-p) *
      ProductMeasure.expectation p (sensitivity f) := by
  unfold totalInfluence sensitivity
  simp_rw [resamplingInfluence_eq]
  rw [← Finset.mul_sum, expectation_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (flipExpectation_eq_pivotal p f i).symm

end Cube
end NarrowDNF.Influence

