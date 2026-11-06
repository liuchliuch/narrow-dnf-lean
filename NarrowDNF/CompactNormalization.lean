import NarrowDNF.Influence
import Mathlib.Tactic.Linarith

namespace NarrowDNF.Influence
open ProductMeasure
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def totalFlipInfluence (p : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  ∑ i, probability p (fun x => f x ≠ f (Function.update x i (!(x i))))

theorem totalFlipInfluence_eq_expected_sensitivity (p : ℝ) (f : (ι → Bool) → Bool) :
    totalFlipInfluence p f = expectation p (sensitivity f) := by
  unfold totalFlipInfluence sensitivity
  rw [Influence.expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold probability
  congr 1
  funext x
  by_cases h : f x = f (Function.update x i (!(x i))) <;> simp [FiberShift.mismatch,h]

/-- The direct normalization used in the revised all-bias proof: the relative
boundary bounds bit-flip influence by `c / p`, without a compact-bias loss. -/
theorem totalFlipInfluence_le_of_relativeBoundary {p c : ℝ} (hp : 0 < p)
    (f : (ι → Bool) → Bool) (hboundary : p * expectation p (sensitivity f) ≤ c) :
    totalFlipInfluence p f ≤ c / p := by
  rw [totalFlipInfluence_eq_expected_sensitivity]
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hboundary)

/-- In the high-bias branch the revised manuscript obtains the dimension- and
bias-uniform bound `totalFlipInfluence ≤ c / p < 2 * c` directly. -/
theorem highBias_totalFlipInfluence_lt {p c : ℝ} (hp : 1 / 2 < p) (hc : 0 < c)
    (f : (ι → Bool) → Bool) (hboundary : p * expectation p (sensitivity f) ≤ c) :
    totalFlipInfluence p f ≤ c / p ∧ c / p < 2 * c := by
  have hp0 : 0 < p := by linarith
  refine ⟨totalFlipInfluence_le_of_relativeBoundary hp0 f hboundary, ?_⟩
  apply (div_lt_iff₀ hp0).mpr
  nlinarith [mul_pos hc (sub_pos.mpr hp)]

/-- Convert a bit-flip bound to the project's resampling convention. The
Bernoulli factor is at most one half throughout the probability interval. -/
theorem totalInfluence_le_half_totalFlipInfluence {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → Bool) :
    totalInfluence p f ≤ (1 / 2 : ℝ) * totalFlipInfluence p f := by
  rw [totalFlipInfluence_eq_expected_sensitivity, totalInfluence_eq_sensitivity]
  apply mul_le_mul_of_nonneg_right
  · nlinarith [sq_nonneg (p - 1 / 2)]
  · apply expectation_nonneg hp0 hp1
    intro x
    unfold sensitivity
    apply Finset.sum_nonneg
    intro i _
    unfold FiberShift.mismatch
    split <;> norm_num

/-- The compact-interval conversion used in the original arXiv all-bias proof.
It remains available, while the revised proof uses the direct relative-boundary
bound above. -/
theorem compact_totalFlipInfluence_le {lam p K : ℝ}
    (hlam : 0 < lam) (hlamHalf : lam ≤ 1/2) (hp0 : lam ≤ p) (hp1 : p ≤ 1-lam)
    (f : (ι → Bool) → Bool) (hI : totalInfluence p f ≤ K) :
    totalFlipInfluence p f ≤ K / (2*lam*(1-lam)) := by
  rw [totalFlipInfluence_eq_expected_sensitivity]
  have hp : 0 ≤ p := hlam.le.trans hp0
  have hpone : p ≤ 1 := by linarith
  have hs : 0 ≤ expectation p (sensitivity f) := by
    apply expectation_nonneg hp hpone
    intro x
    unfold sensitivity
    apply Finset.sum_nonneg
    intro i _
    unfold FiberShift.mismatch
    split <;> norm_num
  have hprod : lam*(1-lam) ≤ p*(1-p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr hp1)]
  have hd : 0 < 2*lam*(1-lam) := by
    apply mul_pos (mul_pos (by norm_num) hlam)
    linarith
  apply (le_div_iff₀ hd).mpr
  have hn := totalInfluence_eq_sensitivity p f
  have hm := mul_le_mul_of_nonneg_right hprod hs
  nlinarith

end NarrowDNF.Influence
