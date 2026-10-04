import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# An auxiliary inequality in the cited Hatami proof

This file certifies a counterexample to the coefficient bound printed at the
start of Section 4, Annals of Mathematics 176 (2012), page 517. It does NOT
refute Hatami's theorem or any numbered theorem of arXiv:2609.00240v1.

The definitions use the actual normalized p-biased basis and the actual product
probability weights, rather than assuming a formula for the Fourier coefficient.
-/

noncomputable section

namespace NarrowDNF.HatamiCoefficientCounterexample

def p : ℝ := 1 / 10

def mass (b : Bool) : ℝ := if b then p else 1 - p

def normalizedBasis (b : Bool) : ℝ :=
  if b then Real.sqrt ((1 - p) / p) else -Real.sqrt (p / (1 - p))

def xorValue (a b : Bool) : ℝ := if a = b then 0 else 1

def coefficient : ℝ :=
  ∑ a : Bool, ∑ b : Bool,
    mass a * mass b * xorValue a b * normalizedBasis a * normalizedBasis b

theorem basis_false : normalizedBasis false = -(1 / 3 : ℝ) := by
  norm_num [normalizedBasis, p]

theorem basis_true : normalizedBasis true = (3 : ℝ) := by
  norm_num [normalizedBasis, p]

theorem coefficient_value : coefficient = -(9 / 50 : ℝ) := by
  norm_num [coefficient, Fintype.sum_bool, mass, xorValue, basis_false, basis_true, p]

/-- This is exactly the claimed bound with |S|=2, whose exponent is 2/2=1. -/
theorem claimed_bound_is_false : ¬ |coefficient| ≤ p := by
  rw [coefficient_value]
  norm_num [p]

theorem bias_in_paper_range : 0 < p ∧ p ≤ (1 / 2 : ℝ) := by
  norm_num [p]

end NarrowDNF.HatamiCoefficientCounterexample
