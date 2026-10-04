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

/-- The exact compact-interval bit-flip bound printed in the all-bias proof,
not the weaker but sufficient lambda-squared bound used by the junta proof. -/
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
