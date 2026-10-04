import NarrowDNF.Influence
import NarrowDNF.CoordinateShift
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
namespace NarrowDNF
namespace Russo
open ProductMeasure Influence
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bitDerivative (b : Bool) : ℝ := if b then 1 else -1

theorem bitWeight_hasDerivAt (b : Bool) (p : ℝ) :
    HasDerivAt (fun q => bitWeight q b) (bitDerivative b) p := by
  cases b
  · simpa [bitWeight, bitDerivative] using (hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p)
  · simpa [bitWeight, bitDerivative] using hasDerivAt_id p

theorem erased_weight (p : ℝ) (i : ι) (x : Cube ι) :
    (∏ j ∈ Finset.univ.erase i, bitWeight p (x j)) =
      weight p (fun j : {j // j ≠ i} => x j) := by
  exact Finset.prod_subtype (Finset.univ.erase i) (by simp [ne_comm]) _

theorem weight_hasDerivAt (p : ℝ) (x : Cube ι) :
    HasDerivAt (fun q => weight q x)
      (∑ i, weight p (fun j : {j // j ≠ i} => x j) * bitDerivative (x i)) p := by
  have h := HasDerivAt.fun_finset_prod (u := Finset.univ)
    (fun i _ => bitWeight_hasDerivAt (x i) p)
  simpa only [weight, smul_eq_mul, erased_weight] using h

theorem signed_sum_fiber (p : ℝ) (i : ι) (F : Cube ι → ℝ) :
    (∑ x : Cube ι, weight p (fun j : {j // j ≠ i} => x j) * bitDerivative (x i) * F x) =
      expectation p (fun z => F (insertBit i true z) - F (insertBit i false z)) := by
  have h := Fintype.sum_equiv (Equiv.funSplitAt i Bool)
    (fun x : Cube ι => weight p (fun j : {j // j ≠ i} => x j) * bitDerivative (x i) * F x)
    (fun t : Bool × ({j // j ≠ i} → Bool) => weight p t.2 * bitDerivative t.1 * F (insertBit i t.1 t.2))
    (fun x => by
      have hin : insertBit i (x i) (fun j : {j // j ≠ i} => x j) = x :=
        (Equiv.funSplitAt i Bool).symm_apply_apply x
      change _ = weight p (fun j : {j // j ≠ i} => x j) * bitDerivative (x i) *
        F (insertBit i (x i) (fun j : {j // j ≠ i} => x j))
      rw [hin])
  rw [h, Fintype.sum_prod_type, Fintype.sum_bool]
  unfold expectation
  simp [bitDerivative, mul_add, Finset.sum_add_distrib, sub_eq_add_neg]

/-- Derivative of an arbitrary finite-cube expectation, obtained by actual
product differentiation and coordinate summation. -/
theorem expectation_hasDerivAt (p : ℝ) (F : Cube ι → ℝ) :
    HasDerivAt (fun q => expectation q F)
      (∑ i, expectation p (fun z => F (insertBit i true z) - F (insertBit i false z))) p := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun x _ => (weight_hasDerivAt p x).mul_const (F x))
  convert h using 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (signed_sum_fiber p i F).symm


private theorem monotone_fiber_difference (a b : Bool) (hab : a ≤ b) :
    boolValue b - boolValue a = FiberShift.mismatch a b := by
  cases a <;> cases b <;> norm_num [boolValue, FiberShift.mismatch] at *

/-- The finite Margulis–Russo identity: the derivative of the acceptance
probability is expected bit-flip sensitivity for an increasing function. -/
theorem monotone_expectation_hasDerivAt (p : ℝ) (f : Cube ι → Bool) (hf : Monotone f) :
    HasDerivAt (fun q => expectation q (fun x => boolValue (f x)))
      (expectation p (sensitivity f)) p := by
  have h := expectation_hasDerivAt p (fun x => boolValue (f x))
  convert h using 1
  unfold sensitivity
  rw [Influence.expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [flipExpectation_eq_pivotal]
  unfold pivotalProbability
  congr 1
  funext z
  symm
  apply monotone_fiber_difference
  have hmono := coordinateMonotone_of_monotone hf i (insertBit i false z)
  simpa [lowerInput, upperInput, Influence.update_insertBit] using hmono

theorem totalInfluence_eq_deriv (p : ℝ) (f : Cube ι → Bool) (hf : Monotone f) :
    totalInfluence p f = 2*p*(1-p) *
      deriv (fun q => expectation q (fun x => boolValue (f x))) p := by
  rw [(monotone_expectation_hasDerivAt p f hf).deriv]
  exact totalInfluence_eq_sensitivity p f

/-- The relative boundary is the derivative on logarithmic bias scale. -/
theorem relativeBoundary_eq_log_deriv {p : ℝ} (hp : 0 < p)
    (f : Cube ι → Bool) (hf : Monotone f) :
    p * expectation p (sensitivity f) =
      deriv (fun t => expectation (Real.exp t) (fun x => boolValue (f x))) (Real.log p) := by
  have h := (monotone_expectation_hasDerivAt (Real.exp (Real.log p)) f hf).comp (Real.log p)
    (Real.hasDerivAt_exp (Real.log p))
  simpa [Real.exp_log hp, Function.comp_def, mul_comm] using h.deriv.symm

end Russo
end NarrowDNF
