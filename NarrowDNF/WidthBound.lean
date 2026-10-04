import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit width and error-budget arithmetic

These are the final arithmetic estimates in the proof of Theorem 1.2 of
arXiv:2609.00240v1. The source's numerical constants are retained. This
module does not assume or assert the structural theorem supplying the
approximator and activation family.
-/

noncomputable section

namespace NarrowDNF.WidthBound

def influenceCeil (K : ℝ) : ℕ := Nat.ceil K

def degree (K ε : ℝ) : ℕ := Nat.ceil (4000 * (influenceCeil K : ℝ) / ε)

def loadBound (K ε : ℝ) : ℝ :=
  Real.exp (160000000000 * (influenceCeil K : ℝ)^2 / ε^2)

def width (K ε : ℝ) : ℕ := Nat.ceil (4 * (2 : ℝ)^(degree K ε) * loadBound K ε / ε)

/-- One explicit absolute constant; no dependence on dimension or bias. -/
def absoluteConstant : ℝ := 10000000000000

theorem absoluteConstant_pos : 0 < absoluteConstant := by norm_num [absoluteConstant]

theorem two_pow_le_exp (d : ℕ) : (2 : ℝ)^d ≤ Real.exp (d : ℝ) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp 1]
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo d
  simpa only [← Real.exp_nat_mul, mul_one] using h

/-- Absorb the ceiling and the prefactor without taking logarithms. -/
theorem ceil_width_le_exp {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (d : ℕ) :
    (Nat.ceil (4 * (2 : ℝ)^d * Real.exp a / ε) : ℝ) ≤
      Real.exp (4 / ε + (d : ℝ) + a) := by
  have hpow : 1 ≤ (2 : ℝ)^d := one_le_pow₀ (by norm_num)
  have hexp : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha
  have hproduct : 1 ≤ (2 : ℝ)^d * Real.exp a := one_le_mul_of_one_le_of_one_le hpow hexp
  have hceil := (Nat.ceil_lt_add_one (by positivity :
    0 ≤ 4 * (2 : ℝ)^d * Real.exp a / ε)).le
  calc
    (Nat.ceil (4 * (2 : ℝ)^d * Real.exp a / ε) : ℝ)
        ≤ 4 * (2 : ℝ)^d * Real.exp a / ε + 1 := hceil
    _ ≤ (4 / ε + 1) * ((2 : ℝ)^d * Real.exp a) := by
      calc
        _ ≤ 4 * (2 : ℝ)^d * Real.exp a / ε + (2 : ℝ)^d * Real.exp a :=
          add_le_add_left hproduct _
        _ = _ := by ring
    _ ≤ Real.exp (4 / ε) * ((2 : ℝ)^d * Real.exp a) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp (4 / ε)) (by positivity)
    _ ≤ Real.exp (4 / ε) * (Real.exp (d : ℝ) * Real.exp a) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right (two_pow_le_exp d) (Real.exp_pos _).le
    _ = Real.exp (4 / ε + (d : ℝ) + a) := by rw [Real.exp_add, Real.exp_add]; ring

/-- The source's explicit width is bounded by one absolute exponential. -/
theorem width_le_exponential {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (hε1 : ε < 1) :
    (width K ε : ℝ) ≤ Real.exp (absoluteConstant * (K + 1)^2 / ε^2) := by
  let R : ℝ := (K + 1) / ε
  let c : ℝ := influenceCeil K
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hc : c ≤ K + 1 := (Nat.ceil_lt_add_one hK.le).le
  have hR : 1 ≤ R := by
    apply (le_div_iff₀ hε).mpr
    dsimp
    linarith
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hR_sq : R ≤ R^2 := by nlinarith
  have hrecip : 1 / ε ≤ R := div_le_div_of_nonneg_right (by linarith) hε.le
  have hcr : c / ε ≤ R := div_le_div_of_nonneg_right hc hε.le
  have hcr0 : 0 ≤ c / ε := div_nonneg hc0 hε.le
  have hcr_sq : (c / ε)^2 ≤ R^2 := by nlinarith
  have hdegree : (degree K ε : ℝ) ≤ 4000 * R + 1 := by
    have hd := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4000 * c / ε)).le
    have heq : 4000 * c / ε = 4000 * (c / ε) := by ring
    rw [heq] at hd
    change (Nat.ceil (4000 * c / ε) : ℝ) ≤ _
    rw [heq]
    linarith
  have hdegree_sq : (degree K ε : ℝ) ≤ 4001 * R^2 := by nlinarith
  have hload : 160000000000 * c^2 / ε^2 ≤ 160000000000 * R^2 := by
    have heq : 160000000000 * c^2 / ε^2 = 160000000000 * (c / ε)^2 := by ring
    rw [heq]
    nlinarith
  have hexponent : 4 / ε + (degree K ε : ℝ) + 160000000000 * c^2 / ε^2 ≤
      absoluteConstant * (K + 1)^2 / ε^2 := by
    have heq : absoluteConstant * (K + 1)^2 / ε^2 = absoluteConstant * R^2 := by
      dsimp [R]
      ring
    rw [heq]
    unfold absoluteConstant
    have hrecip4 : 4 / ε ≤ 4 * R^2 := by
      calc
        4 / ε = 4 * (1 / ε) := by ring
        _ ≤ 4 * R := mul_le_mul_of_nonneg_left hrecip (by norm_num)
        _ ≤ 4 * R^2 := mul_le_mul_of_nonneg_left hR_sq (by norm_num)
    nlinarith [sq_nonneg R]
  exact (ceil_width_le_exp hε (by positivity) (degree K ε)).trans
    (Real.exp_le_exp.mpr hexponent)

/-- An explicit witness for the absolute-constant quantifier in the width bound. -/
theorem exists_absolute_width_constant : ∃ C : ℝ, 0 < C ∧
    ∀ K ε : ℝ, 0 < K → 0 < ε → ε < 1 →
      (width K ε : ℝ) ≤ Real.exp (C * (K + 1)^2 / ε^2) :=
  ⟨absoluteConstant, absoluteConstant_pos, fun _ _ hK hε hε1 =>
    width_le_exponential hK hε hε1⟩

/-- The selection bound with `e = τ = ε/4` gives the stated active-set cost. -/
theorem selection_load_bound {p ε L : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hε : 0 < ε) (hL : 0 ≤ L) (d : ℕ) :
    (2-p)^d * L * (1 + (ε/4)/(ε/4)) ≤ (2 : ℝ)^(d+1) * L := by
  have hpow : (2-p)^d ≤ (2 : ℝ)^d :=
    pow_le_pow_left₀ (by linarith) (by linarith) d
  have hdiv : (ε/4)/(ε/4) = 1 := div_self (by positivity)
  rw [hdiv, pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right hpow hL]

/-- Markov truncation consumes at most half the target error budget. -/
theorem truncation_budget {ε L M : ℝ} (hε : 0 < ε) (d : ℕ)
    (hM : M ≤ (2 : ℝ)^(d+1) * L) :
    M / ((Nat.ceil (4 * (2 : ℝ)^d * L / ε) : ℝ) + 1) ≤ ε/2 := by
  have hceil := Nat.le_ceil (4 * (2 : ℝ)^d * L / ε)
  have hmul := (div_le_iff₀ hε).mp hceil
  apply (div_le_iff₀ (by positivity)).mpr
  rw [pow_succ] at hM
  nlinarith

/-- The triangle inequality plus the two source error budgets totals at most `ε`. -/
theorem triangle_truncation_budget {ε L M a b : ℝ} (hε : 0 < ε) (d : ℕ)
    (ha : a ≤ ε/4 + ε/4)
    (hb : b ≤ M / ((Nat.ceil (4 * (2 : ℝ)^d * L / ε) : ℝ) + 1))
    (hM : M ≤ (2 : ℝ)^(d+1) * L) : a + b ≤ ε := by
  have ht := truncation_budget hε d hM
  linarith

end NarrowDNF.WidthBound
