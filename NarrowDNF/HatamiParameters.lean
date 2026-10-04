import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Explicit numerical bounds for the parameters in Appendix A. -/
noncomputable section
namespace NarrowDNF.HatamiParameters

def delta (k : ℝ) : ℝ := (2 : ℝ) ^ (-(100 : ℝ) * k^2)
def epsilonOne (k e0 : ℝ) : ℝ := (3 : ℝ) ^ (-(10 : ℝ)*k^2) * e0 ^ ((10 : ℝ)*k)
def loadExpression (k e0 : ℝ) : ℝ := k * (2 : ℝ) ^ ((2 : ℝ)*k) / (delta k * (epsilonOne k e0)^2)

theorem delta_pos (k : ℝ) : 0 < delta k := Real.rpow_pos_of_pos (by norm_num) _
theorem epsilonOne_pos {e0 : ℝ} (he0 : 0 < e0) (k : ℝ) : 0 < epsilonOne k e0 :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos he0 _)

theorem log_inverse_lower {e0 k : ℝ} (he0 : 0 < e0) (hk : e0⁻¹ ≤ k) :
    -Real.log e0 ≤ k := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr he0)
  rw [Real.log_inv] at h
  linarith

/-- A conservative bound that directly fits the paper's stated final L,
without changing δ or ε₁. -/
theorem loadExpression_le_exp {e0 k : ℝ} (he0 : 0 < e0) (hk1 : 1 ≤ k)
    (hk : e0⁻¹ ≤ k) : loadExpression k e0 ≤ Real.exp (10000*k^2) := by
  have hk0 : 0 < k := by linarith
  have hd := delta_pos k
  have he := epsilonOne_pos he0 k
  have hratio : 0 < loadExpression k e0 := by
    unfold loadExpression
    exact div_pos (mul_pos hk0 (Real.rpow_pos_of_pos (by norm_num) _)) (mul_pos hd (sq_pos_of_pos he))
  have hlog2 : Real.log 2 ≤ 1 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1; norm_num
  have hlog3 : Real.log 3 ≤ 2 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3) using 1; norm_num
  have hlogk : Real.log k ≤ k := by linarith [Real.log_le_sub_one_of_pos hk0]
  have hloge := log_inverse_lower he0 hk
  have hlog : Real.log (loadExpression k e0) ≤ 10000*k^2 := by
    calc
      Real.log (loadExpression k e0) = Real.log k + (2*k+100*k^2)*Real.log 2 +
          20*k^2*Real.log 3 + 20*k*(-Real.log e0) := by
        unfold loadExpression delta epsilonOne
        rw [Real.log_div, Real.log_mul, Real.log_mul, Real.log_pow, Real.log_mul]
        · rw [Real.log_rpow (by norm_num : (0:ℝ)<2), Real.log_rpow (by norm_num : (0:ℝ)<2),
            Real.log_rpow (by norm_num : (0:ℝ)<3), Real.log_rpow he0]
          ring
        all_goals positivity
      _ ≤ k + (2*k+100*k^2)*1 + 20*k^2*2 + 20*k*k := by gcongr
      _ ≤ 10000*k^2 := by nlinarith [sq_nonneg (k-1)]
  exact (Real.log_le_iff_le_exp hratio).mp hlog


/-- The final L bound with exactly Appendix A's parameter definitions. -/
theorem paper_load_bound {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hC : 1 ≤ C) :
    loadExpression (1000*C/a) (a/1000) ≤ Real.exp (10000000000*C^2/a^2) := by
  have he0 : 0 < a/1000 := by positivity
  have hk1 : (1:ℝ) ≤ 1000*C/a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  have hk : (a/1000)⁻¹ ≤ 1000*C/a := by
    rw [inv_div]
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith
  have h := loadExpression_le_exp he0 hk1 hk
  convert h using 1; congr 1; ring


/-- Corrected cross-term expression after retaining the missing 2^|S| factor
in the external Hatami coefficient bound. -/
def correctedCrossExpression (k e0 : ℝ) : ℝ :=
  (2 : ℝ)^((9:ℝ)*k) * delta k / (epsilonOne k e0)^2

theorem corrected_cross_bound {e0 k : ℝ} (he0 : 0 < e0) (hk1 : 1 ≤ k)
    (hk : e0⁻¹ ≤ k) : correctedCrossExpression k e0 ≤ e0 := by
  have hk0 : 0 < k := by linarith
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have h2low : (1:ℝ)/2 ≤ Real.log 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [Real.log_inv] at this
    norm_num at this
    linarith
  have h3 : Real.log 3 ≤ (3:ℝ)/2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(3:ℝ)/2)
    rw [Real.log_div (by norm_num : (3:ℝ)≠0) (by norm_num : (2:ℝ)≠0)] at h
    linarith
  have hlogk : Real.log k ≤ k/2 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hk0 (by norm_num : (0:ℝ)<2))
    rw [Real.log_div hk0.ne' (by norm_num : (2:ℝ)≠0)] at h
    linarith
  have hloge : -Real.log e0 ≤ k/2 := by
    have h := Real.log_le_log (inv_pos.mpr he0) hk
    rw [Real.log_inv] at h
    exact h.trans hlogk
  have hr : 0 < correctedCrossExpression k e0 := by
    unfold correctedCrossExpression
    exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (delta_pos k))
      (sq_pos_of_pos (epsilonOne_pos he0 k))
  apply (Real.log_le_log_iff hr he0).mp
  have heq : Real.log (correctedCrossExpression k e0) =
      9*k*Real.log 2 - 100*k^2*Real.log 2 + 20*k^2*Real.log 3 + 20*k*(-Real.log e0) := by
    unfold correctedCrossExpression delta epsilonOne
    rw [Real.log_div, Real.log_mul, Real.log_pow, Real.log_mul]
    · rw [Real.log_rpow (by norm_num : (0:ℝ)<2), Real.log_rpow (by norm_num : (0:ℝ)<2),
        Real.log_rpow (by norm_num : (0:ℝ)<3), Real.log_rpow he0]
      ring
    all_goals positivity
  rw [heq]
  have hA := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 9*k)
  have hB := mul_le_mul_of_nonneg_left h2low (by positivity : 0 ≤ 100*k^2)
  have hC := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 20*k^2)
  have hD := mul_le_mul_of_nonneg_left hloge (by positivity : 0 ≤ 20*k)
  nlinarith [sq_nonneg (k-1)]

end NarrowDNF.HatamiParameters
