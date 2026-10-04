import NarrowDNF.LoadTransport
import NarrowDNF.ShiftProbability
import NarrowDNF.Weighted

noncomputable section
namespace NarrowDNF
namespace Activation
open ProductMeasure ShiftProbability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The set of lower shifts along a covering coordinate order is exactly the
set represented by the Bernoulli choice vector. -/
theorem lowerCoordinates_map_choices (order : List ι) (D : Cube ι) (i : ι) :
    i ∈ lowerCoordinates (order.map fun j => (j, D j)) ↔ i ∈ order ∧ D i = true := by
  induction order with
  | nil => simp [lowerCoordinates]
  | cons j rest ih =>
    cases hj : D j <;> by_cases hij : i = j <;>
      simp_all [lowerCoordinates]

theorem lowerCoordinates_cover (order : List ι) (horder : ∀ i, i ∈ order) (D : Cube ι) :
    lowerCoordinates (order.map fun i => (i, D i)) = forcingCoordinates D := by
  ext i
  simp [lowerCoordinates_map_choices, horder, forcingCoordinates]

/-- Theorem 3.4 of arXiv:2609.00240v1, with explicit finite random choices,
full adaptive measurability, and the zero-load edge case included. -/
theorem controlled_monotonicization {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {d : ℕ} {e L : ℝ} (_he0 : 0 ≤ e) (hL0 : 0 ≤ L)
    {f : Cube ι → Bool} (hf : Monotone f)
    {J : Activation ι} (hJ : J.Increasing) (hd : J.ArityLE d)
    {h : Cube ι → Bool} (hh : J.Measurable h)
    (he : error p f h ≤ e) (hL : J.load p ≤ L)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ (D : Finset ι) (u : Cube ι → Bool),
      Monotone u ∧ (J.force D).Measurable u ∧ error p f u ≤ e + τ ∧
      expectation p (fun x => (((J.force D).activeFinset x).card : ℝ)) ≤
        (2-p)^d * L * (1 + e / τ) := by
  classical
  let order := (Finset.univ : Finset ι).toList
  have hn : order.Nodup := Finset.nodup_toList _
  have hc : ∀ i, i ∈ order := by intro i; simp [order]
  let H := fun D : Cube ι => shiftByChoices order D h
  let cost := fun D : Cube ι =>
    expectation p (fun x => (((J.force (forcingCoordinates D)).activeFinset x).card : ℝ))
  have hcost : ∀ D, 0 ≤ cost D := by
    intro D
    exact expectation_nonneg hp0.le hp1.le (fun x => Nat.cast_nonneg _)
  have hcostMean : expectation p cost ≤ (2-p)^d * L := by
    calc
      expectation p cost ≤ expectation p (fun D : Cube ι =>
          (J.force (forcingCoordinates D)).load p) :=
        expectation_mono hp0.le hp1.le (fun D => expected_active_le_load _ hp0.le hp1.le)
      _ = J.load (2*p-p^2) := load_forced_mean J p
      _ ≤ (2-p)^d * J.load p := load_forcing_le J hp0.le hp1.le hd
      _ ≤ (2-p)^d * L := mul_le_mul_of_nonneg_left hL (pow_nonneg (by linarith : (0:ℝ) ≤ 2-p) d)
  have herrMean : expectation p (fun D => error p f (H D)) ≤ e :=
    (iterated_error_le p hp0.le hp1.le order hn f h hf).trans he
  obtain ⟨D, hDe, hDc⟩ := Weighted.select_two_budgets
    (weight p) (weight_pos hp0 hp1) (sum_weight p)
    (fun D => error p f (H D)) cost
    (fun D => probability_nonneg hp0.le hp1.le _) hcost
    e ((2-p)^d * L) τ (mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ 2-p) d) hL0) hτ herrMean hcostMean
  refine ⟨forcingCoordinates D, H D, shiftByChoices_monotone order hc D h, ?_, hDe, hDc⟩
  have hm := measurable_applyShifts (order.map fun i => (i, D i)) hJ hh
  rw [lowerCoordinates_cover order hc D] at hm
  exact hm

end Activation
end NarrowDNF
