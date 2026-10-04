import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bias-matched shifts on a Boolean fiber

This file proves the two-point calculation used in Lemma 3.1 of
arXiv:2609.00240v1. The probability of the upper shift is `1 - p` and the
probability of the lower shift is `p`; the input fiber has the same bias `p`.

The error theorem is a conditional, single-fiber statement. Passing to an
arbitrary Boolean cube requires a separate summation/integration argument.
-/

namespace NarrowDNF.FiberShift

@[simp] private theorem true_not_le_false : ¬ ((true : Bool) ≤ false) := by decide

/-- Values at the lower and upper endpoints of one coordinate fiber. -/
abbrev Fiber := Bool × Bool

/-- The real-valued indicator that two Boolean values disagree. -/
def mismatch (a b : Bool) : ℝ := if a = b then 0 else 1

/-- Conditional error on one fiber under a `p`-biased input. -/
def error (p : ℝ) (f v : Fiber) : ℝ :=
  (1 - p) * mismatch f.1 v.1 + p * mismatch f.2 v.2

/-- The upper shift changes the decreasing fiber `10` to `11`. -/
def upper (v : Fiber) : Fiber := (v.1, v.1 || v.2)

/-- The lower shift changes the decreasing fiber `10` to `00`. -/
def lower (v : Fiber) : Fiber := (v.1 && v.2, v.2)

/-- An upper-shifted fiber is nondecreasing. -/
theorem upper_monotone (v : Fiber) : (upper v).1 ≤ (upper v).2 := by
  rcases v with ⟨v0, v1⟩
  cases v0 <;> cases v1 <;> decide

/-- A lower-shifted fiber is nondecreasing. -/
theorem lower_monotone (v : Fiber) : (lower v).1 ≤ (lower v).2 := by
  rcases v with ⟨v0, v1⟩
  cases v0 <;> cases v1 <;> decide

/-- The upper shift fixes any already nondecreasing fiber. -/
theorem upper_eq_self_of_monotone (v : Fiber) (hv : v.1 ≤ v.2) :
    upper v = v := by
  rcases v with ⟨v0, v1⟩
  cases v0 <;> cases v1 <;> simp_all [upper]

/-- The lower shift fixes any already nondecreasing fiber. -/
theorem lower_eq_self_of_monotone (v : Fiber) (hv : v.1 ≤ v.2) :
    lower v = v := by
  rcases v with ⟨v0, v1⟩
  cases v0 <;> cases v1 <;> simp_all [lower]

/-- The upper shift preserves componentwise ordering between two fibers.
This is the local fact needed to preserve monotonicity in another coordinate. -/
theorem upper_preserves_order (v w : Fiber)
    (h0 : v.1 ≤ w.1) (h1 : v.2 ≤ w.2) :
    (upper v).1 ≤ (upper w).1 ∧ (upper v).2 ≤ (upper w).2 := by
  rcases v with ⟨v0, v1⟩
  rcases w with ⟨w0, w1⟩
  cases v0 <;> cases v1 <;> cases w0 <;> cases w1 <;>
    simp_all [upper]

/-- The lower shift preserves componentwise ordering between two fibers.
This is the local fact needed to preserve monotonicity in another coordinate. -/
theorem lower_preserves_order (v w : Fiber)
    (h0 : v.1 ≤ w.1) (h1 : v.2 ≤ w.2) :
    (lower v).1 ≤ (lower w).1 ∧ (lower v).2 ≤ (lower w).2 := by
  rcases v with ⟨v0, v1⟩
  rcases w with ⟨w0, w1⟩
  cases v0 <;> cases v1 <;> cases w0 <;> cases w1 <;>
    simp_all [lower]

/-- Exact error improvement: only the target fiber `01` paired with the
approximating fiber `10` gives a strict improvement when `0 < p < 1`. -/
theorem randomized_error_eq_sub (p : ℝ) (f v : Fiber) (hf : f.1 ≤ f.2) :
    (1 - p) * error p f (upper v) + p * error p f (lower v) =
      error p f v -
        (if f = (false, true) ∧ v = (true, false) then 2 * p * (1 - p) else 0) := by
  rcases f with ⟨f0, f1⟩
  rcases v with ⟨v0, v1⟩
  cases f0 <;> cases f1 <;> cases v0 <;> cases v1 <;>
    simp_all [error, mismatch, upper, lower] <;> ring

/-- The bias-matched randomized shift does not increase conditional error
against a nondecreasing target fiber. The closed interval also includes the
degenerate biases, strengthening the paper's `0 < p < 1` hypothesis. -/
theorem randomized_error_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f v : Fiber) (hf : f.1 ≤ f.2) :
    (1 - p) * error p f (upper v) + p * error p f (lower v) ≤ error p f v := by
  rw [randomized_error_eq_sub p f v hf]
  by_cases h : f = (false, true) ∧ v = (true, false)
  · simp only [if_pos h]
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
  · simp [h]

end NarrowDNF.FiberShift
