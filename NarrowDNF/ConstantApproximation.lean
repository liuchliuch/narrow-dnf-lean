import NarrowDNF.Fourier
import NarrowDNF.Adaptive

namespace NarrowDNF
open ProductMeasure Influence
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem error_false (p : ℝ) (f : Cube ι → Bool) :
    error p f (fun _ => false) = expectation p (fun x => boolValue (f x)) := by
  unfold error probability
  congr 1
  funext x
  cases hfx : f x <;> simp [hfx, boolValue]

theorem error_true (p : ℝ) (f : Cube ι → Bool) :
    error p f (fun _ => true) = 1 - expectation p (fun x => boolValue (f x)) := by
  have h : (fun x => if f x ≠ true then (1:ℝ) else 0) =
      (fun x => 1 - boolValue (f x)) := by
    funext x
    cases hfx : f x <;> simp [boolValue]
  unfold error probability
  rw [h]
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

/-- A Boolean function is close to one of the constants whenever its variance
is small, with the exact factor used in the all-bias argument. -/
theorem exists_constant_error_le_twice_variance {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Cube ι → Bool) :
    ∃ b : Bool, error p f (fun _ => b) ≤ 2 * variance p (fun x => boolValue (f x)) := by
  let a := expectation p (fun x => boolValue (f x))
  have ha0 : 0 ≤ a := expectation_nonneg hp0 hp1 (fun x => by cases hfx : f x <;> simp [boolValue])
  have ha1 : a ≤ 1 := by
    rw [← expectation_one (ι := ι) p]
    exact expectation_mono hp0 hp1 (fun x => by cases hfx : f x <;> simp [boolValue])
  rw [variance_bool_eq]
  by_cases ha : a ≤ 1/2
  · refine ⟨false, ?_⟩
    rw [error_false]
    change a ≤ 2*(a*(1-a))
    nlinarith
  · refine ⟨true, ?_⟩
    rw [error_true]
    change 1-a ≤ 2*(a*(1-a))
    nlinarith

/-- The high-bias near-one branch in the proof of Conjecture 1.1. -/
theorem near_one_constant_approximation {p c ε : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hc : 0 < c)
    (f : Cube ι → Bool)
    (hboundary : p * expectation p (sensitivity f) ≤ c)
    (hnear : 1-p ≤ ε/(2*c)) :
    ∃ b : Bool, error p f (fun _ => b) ≤ ε := by
  obtain ⟨b, hb⟩ := exists_constant_error_le_twice_variance hp0.le hp1.le f
  refine ⟨b, hb.trans ?_⟩
  have hpoincare := Fourier.poincare hp0 hp1 f
  have hI := totalInfluence_eq_sensitivity p f
  have hmul := mul_le_mul_of_nonneg_left hboundary (sub_nonneg.mpr hp1.le)
  have hnear' := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hc)).mp hnear
  nlinarith

end NarrowDNF
