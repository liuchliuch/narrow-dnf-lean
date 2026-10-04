import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NarrowDNF
namespace Weighted
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Integer-threshold Markov inequality for arbitrary finite nonnegative weights.
No probability normalization is needed for this inequality. -/
theorem integer_markov (weights : α → ℝ) (hw : ∀ x, 0 ≤ weights x)
    (size : α → ℕ) (cutoff : ℕ) :
    (∑ x, weights x * (if cutoff < size x then 1 else 0)) ≤
      (∑ x, weights x * (size x : ℝ)) / (cutoff + 1 : ℝ) := by
  have hd : (0 : ℝ) < cutoff + 1 := by positivity
  apply (le_div_iff₀ hd).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : cutoff < size x
  · simp only [if_pos h, mul_one]
    have hs : (cutoff : ℝ) + 1 ≤ size x := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_left hs (hw x)
  · simp only [if_neg h, mul_zero, zero_mul]
    exact mul_nonneg (hw x) (Nat.cast_nonneg _)

/-- A finite probability average has a realization at most its mean. Strictly
positive weights match the paper's interior Bernoulli biases. -/
theorem exists_le_mean [Nonempty α] (weights : α → ℝ)
    (hw : ∀ x, 0 < weights x) (hs : ∑ x, weights x = 1) (value : α → ℝ) :
    ∃ x, value x ≤ ∑ y, weights y * value y := by
  classical
  by_contra h
  push_neg at h
  let m := ∑ y, weights y * value y
  have hlt : (∑ x, weights x * m) < ∑ x, weights x * value x := by
    apply Finset.sum_lt_sum
    · intro x _
      exact le_of_lt (mul_lt_mul_of_pos_left (h x) (hw x))
    · obtain ⟨x⟩ := ‹Nonempty α›
      exact ⟨x, Finset.mem_univ x, mul_lt_mul_of_pos_left (h x) (hw x)⟩
  have heq : (∑ x, weights x * m) = m := by rw [← Finset.sum_mul, hs, one_mul]
  rw [heq] at hlt
  exact (lt_irrefl m) hlt


/-- Simultaneously select small error and cost by one weighted average.
This is the full finite averaging step of Theorem 3.4, including zero budget. -/
theorem select_two_budgets [Nonempty α] (weights : α → ℝ)
    (hw : ∀ x, 0 < weights x) (hs : ∑ x, weights x = 1)
    (err cost : α → ℝ) (herr : ∀ x, 0 ≤ err x) (hcost : ∀ x, 0 ≤ cost x)
    (e B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ)
    (he : (∑ x, weights x * err x) ≤ e)
    (hM : (∑ x, weights x * cost x) ≤ B) :
    ∃ x, err x ≤ e + τ ∧ cost x ≤ B * (1 + e / τ) := by
  classical
  by_cases hB0 : B = 0
  · obtain ⟨x, hx⟩ := exists_le_mean weights hw hs err
    refine ⟨x, by linarith, ?_⟩
    have hterm : weights x * cost x ≤ ∑ y, weights y * cost y :=
      Finset.single_le_sum (fun y _ => mul_nonneg (hw y).le (hcost y)) (Finset.mem_univ x)
    have hc : cost x ≤ 0 := by nlinarith [hw x]
    simp only [hB0, zero_mul]
    exact hc
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    obtain ⟨x, hx⟩ := exists_le_mean weights hw hs (fun x => err x + (τ / B) * cost x)
    have hsum : (∑ x, weights x * (err x + (τ / B) * cost x)) ≤ e + τ := by
      calc
        _ = (∑ x, weights x * err x) + (τ / B) * (∑ x, weights x * cost x) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ e + (τ / B) * B := add_le_add he
          (mul_le_mul_of_nonneg_left hM (div_nonneg hτ.le hB))
        _ = e + τ := by rw [div_mul_cancel₀ τ hB0]
    have hchoice : err x + (τ / B) * cost x ≤ e + τ := hx.trans hsum
    refine ⟨x, ?_, ?_⟩
    · have := mul_nonneg (div_nonneg hτ.le hB) (hcost x)
      linarith
    · have hc : (τ * cost x) / B ≤ e + τ := by
        rw [← div_mul_eq_mul_div]
        linarith [herr x]
      have hc' := (div_le_iff₀ hBp).mp hc
      have hbound : cost x ≤ ((e + τ) * B) / τ := by
        apply (le_div_iff₀ hτ).mpr
        nlinarith
      have hident : ((e + τ) * B) / τ = B * (1 + e / τ) := by
        calc
          ((e + τ) * B) / τ = B * (e / τ + τ / τ) := by ring
          _ = B * (1 + e / τ) := by rw [div_self hτ.ne']; ring
      simpa only [hident] using hbound

end Weighted
end NarrowDNF
