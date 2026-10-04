import NarrowDNF.BourgainComponents
import NarrowDNF.FourierTruncation
import NarrowDNF.HatamiParameters
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Exact paper-parameter interfaces for Bourgain's estimate

The analytic proof uses a natural degree cutoff. These identities transfer it
to the paper's real cutoff by taking its floor, without changing the activation
family or the paper's epsilon-one parameter.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainRealCutoff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Increasing the smallness threshold increases truncated Fourier mass. -/
theorem smallComponentMass_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → ℝ) (k : ℕ) {η ζ : ℝ} (hη : η ≤ ζ) :
    BourgainComponents.smallComponentMass p f k η ≤
      BourgainComponents.smallComponentMass p f k ζ := by
  apply ProductMeasure.expectation_mono hp0 hp1
  intro x
  apply Finset.sum_le_sum
  intro S _
  by_cases hsmall : |Fourier.component p f S x| ≤ η
  · simp only [if_pos hsmall, if_pos (hsmall.trans hη)]
    exact le_rfl
  · simp only [if_neg hsmall]
    split_ifs <;> positivity

/-- The real-valued cutoff from the paper is exactly its natural floor. -/
theorem smallMassReal_eq_floor {k : ℝ} (hk : 0 ≤ k)
    (p : ℝ) (f : (ι → Bool) → ℝ) (η : ℝ) :
    FourierTruncation.smallMassReal p f k η =
      BourgainComponents.smallComponentMass p f (Nat.floor k) η := by
  unfold FourierTruncation.smallMassReal BourgainComponents.smallComponentMass
  simp_rw [Finset.sum_filter]
  rw [Influence.expectation_sum]
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  funext x
  have hdeg : S.card ≤ Nat.floor k ↔ (S.card : ℝ) ≤ k := Nat.le_floor_iff hk
  by_cases hS : (S.card : ℝ) ≤ k <;> simp [hdeg, hS]

omit [Fintype ι] [DecidableEq ι] in
/-- The paper's exact epsilon-one parameter decreases with nonnegative k. -/
theorem epsilonOne_antitone {e a b : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    HatamiParameters.epsilonOne b e ≤ HatamiParameters.epsilonOne a e := by
  unfold HatamiParameters.epsilonOne
  apply mul_le_mul
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith [sq_nonneg (b-a)]
  · exact Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith)
  · exact Real.rpow_nonneg he.le _
  · exact Real.rpow_nonneg (by norm_num) _

omit [Fintype ι] [DecidableEq ι] in
/-- At an integer cutoff, the paper's real powers equal the natural-power
expression used in the numeric Bourgain calculation. -/
theorem epsilonOne_nat (k : ℕ) (e : ℝ) :
    HatamiParameters.epsilonOne (k : ℝ) e = e^(10*k)/(3 : ℝ)^(10*k^2) := by
  unfold HatamiParameters.epsilonOne
  have hneg : -(10 : ℝ) * (k : ℝ)^2 = -((10*k^2 : ℕ) : ℝ) := by push_cast; ring
  have hpos : (10 : ℝ) * (k : ℝ) = ((10*k : ℕ) : ℝ) := by push_cast; ring
  rw [hneg, hpos, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_natCast, Real.rpow_natCast]
  ring

/-- A direct bound for the source's truncated mass by the natural-cutoff mass
at the matching natural epsilon-one parameter. -/
theorem paper_smallMass_le_natural {p k e : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hk : 0 ≤ k) (he : 0 < e) (he1 : e ≤ 1) (f : (ι → Bool) → ℝ) :
    FourierTruncation.smallMassReal p f k (HatamiParameters.epsilonOne k e) ≤
      BourgainComponents.smallComponentMass p f (Nat.floor k)
        (e^(10*Nat.floor k)/(3 : ℝ)^(10*(Nat.floor k)^2)) := by
  rw [smallMassReal_eq_floor hk]
  apply smallComponentMass_mono hp0 hp1
  rw [← epsilonOne_nat]
  exact epsilonOne_antitone he he1 (Nat.cast_nonneg _) (Nat.floor_le hk)

omit [Fintype ι] [DecidableEq ι] in
/-- The extra factor two in the natural-cutoff error budget pays for replacing
a real cutoff by its floor. -/
theorem floor_errorBudget_le {k e : ℝ} (hk : 1 ≤ k) :
    e^2 / (2 * (Nat.floor k : ℝ)) ≤ e^2 / k := by
  have hk0 : 0 ≤ k := by linarith
  have hm : 1 ≤ Nat.floor k := (Nat.le_floor_iff hk0).mpr (by simpa using hk)
  have hmR : (1 : ℝ) ≤ Nat.floor k := by exact_mod_cast hm
  have hkupper := Nat.lt_floor_add_one k
  have hbound : k ≤ 2 * (Nat.floor k : ℝ) := by linarith
  exact div_le_div_of_nonneg_left (sq_nonneg e) (by linarith) hbound

end NarrowDNF.BourgainRealCutoff
