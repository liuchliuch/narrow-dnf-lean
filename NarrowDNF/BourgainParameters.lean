import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Explicit numerical choices for the reconstructed Bourgain small-component
estimate. The Fourier threshold eta retains the paper's constants. -/

noncomputable section
namespace NarrowDNF.BourgainParameters

def eta (k : ℕ) (e : ℝ) : ℝ := e^(10*k) / (3:ℝ)^(10*k^2)
def tau (k : ℕ) (e : ℝ) : ℝ := e^3 / (3:ℝ)^(6*k)
def realCutoff (k : ℕ) (e : ℝ) : ℝ := (3:ℝ)^(18*k) / e^10
def cutoff (k : ℕ) (e : ℝ) : ℕ := ⌈realCutoff k e⌉₊

theorem cutoff_lower (k : ℕ) (e : ℝ) : realCutoff k e ≤ (cutoff k e : ℝ) :=
  Nat.le_ceil _

theorem realCutoff_ge_one (k : ℕ) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    1 ≤ realCutoff k e := by
  unfold realCutoff
  apply (le_div_iff₀ (pow_pos he0 10)).mpr
  simp only [one_mul]
  exact (pow_le_one₀ he0.le he1).trans (one_le_pow₀ (by norm_num))

theorem cutoff_upper (k : ℕ) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    (cutoff k e : ℝ) ≤ 2 * realCutoff k e := by
  have hR := realCutoff_ge_one k he0 he1
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ realCutoff k e by linarith)
  change (⌈realCutoff k e⌉₊ : ℝ) ≤ _
  linarith

theorem three_pow_ge_eight_sq {k : ℕ} (hk : 5 ≤ k) : 8*k^2 ≤ 3^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 3 k]
    nlinarith

theorem tau_rpow (k : ℕ) {e : ℝ} (he0 : 0 ≤ e) :
    (tau k e) ^ (2/3 : ℝ) = e^2 / (3:ℝ)^(4*k) := by
  unfold tau
  rw [Real.div_rpow (pow_nonneg he0 _) (by positivity),
    ← Real.rpow_natCast_mul he0,
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 3)]
  have h2 : ((6*k : ℕ) : ℝ) * (2/3:ℝ) = ((4*k : ℕ) : ℝ) := by push_cast; ring
  norm_num only [Nat.cast_ofNat]
  rw [h2, Real.rpow_natCast]
  norm_num

/-- The first term remains small after rounding M up to an integer. -/
theorem first_term_le {k : ℕ} (hk : 1 ≤ k) {e : ℝ}
    (he0 : 0 < e) (he1 : e ≤ 1) :
    (cutoff k e : ℝ)^k * (eta k e)^2 ≤ e^2 / (3:ℝ)^k := by
  have hM := pow_le_pow_left₀ (Nat.cast_nonneg (cutoff k e)) (cutoff_upper k he0 he1) k
  have hA : e^(10*k) ≤ e^2 := pow_le_pow_of_le_one he0.le he1 (by omega)
  have hpow : (2:ℝ)^k * (3:ℝ)^(18*k*k) * (3:ℝ)^k ≤ (3:ℝ)^(20*k*k) := by
    calc
      _ ≤ (3:ℝ)^k * (3:ℝ)^(18*k*k) * (3:ℝ)^k := by
        gcongr
        norm_num
      _ = (3:ℝ)^(k+18*k*k+k) := by simp only [pow_add]
      _ ≤ (3:ℝ)^(20*k*k) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hMp : (2*realCutoff k e)^k =
      (2:ℝ)^k * (3:ℝ)^(18*k*k) / e^(10*k) := by
    unfold realCutoff
    simp only [mul_pow, div_pow, ← pow_mul]
    ring
  have heta : (eta k e)^2 = (e^(10*k))^2 / (3:ℝ)^(20*k*k) := by
    unfold eta
    rw [div_pow, ← pow_mul (3:ℝ) (10*k^2) 2]
    congr 1
    congr 1
    ring
  calc
    _ ≤ (2*realCutoff k e)^k * (eta k e)^2 :=
      mul_le_mul_of_nonneg_right hM (sq_nonneg _)
    _ = (2:ℝ)^k * (3:ℝ)^(18*k*k) * e^(10*k) / (3:ℝ)^(20*k*k) := by
      rw [hMp, heta]
      field_simp
    _ ≤ e^2 / (3:ℝ)^k := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      calc
        _ = e^(10*k) * ((2:ℝ)^k * (3:ℝ)^(18*k*k) * (3:ℝ)^k) := by ring
        _ ≤ e^2 * (3:ℝ)^(20*k*k) :=
          mul_le_mul hA hpow (by positivity) (sq_nonneg e)

theorem middle_term_le {k : ℕ} {e C : ℝ} (he0 : 0 ≤ e)
    (_hC0 : 0 ≤ C) (hC : C ≤ k) :
    2*C*(3:ℝ)^(2*k)*(tau k e)^(2/3:ℝ) ≤
      2*(k:ℝ)*e^2/(3:ℝ)^k := by
  calc
    _ = 2*C*e^2/(3:ℝ)^(2*k) := by
      rw [tau_rpow k he0, show 4*k = 2*k+2*k by omega, pow_add]
      field_simp
    _ ≤ 2*(k:ℝ)*e^2/(3:ℝ)^(2*k) := by gcongr
    _ ≤ 2*(k:ℝ)*e^2/(3:ℝ)^k :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega))

theorem sqrt_cutoff_lower (k : ℕ) {e : ℝ} (he0 : 0 < e) :
    (3:ℝ)^(9*k)/e^5 ≤ Real.sqrt (cutoff k e : ℝ) := by
  apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr
  calc
    _ = realCutoff k e := by
      unfold realCutoff
      simp only [div_pow, ← pow_mul]
      congr 1
      congr 1
      ring
    _ ≤ _ := cutoff_lower k e

theorem cutoff_denominator_lower (k : ℕ) {e : ℝ} (he0 : 0 < e) :
    (3:ℝ)^(3*k)/e^2 ≤ Real.sqrt (cutoff k e : ℝ) * tau k e := by
  have hid : ((3:ℝ)^(9*k)/e^5) * tau k e = (3:ℝ)^(3*k)/e^2 := by
    unfold tau
    rw [show 9*k = 6*k+3*k by omega, pow_add, pow_add e 3 2]
    field_simp
  rw [← hid]
  exact mul_le_mul_of_nonneg_right (sqrt_cutoff_lower k he0) (by
    unfold tau
    positivity)

theorem third_term_le {k : ℕ} (hk : 1 ≤ k) {e C : ℝ}
    (he0 : 0 < e) (hC : C ≤ k) :
    (3:ℝ)^(2*k)*Real.sqrt C/(Real.sqrt (cutoff k e : ℝ)*tau k e) ≤
      (k:ℝ)*e^2/(3:ℝ)^k := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hroot : Real.sqrt C ≤ k := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((k:ℝ)-1)]
  calc
    _ ≤ (3:ℝ)^(2*k)*Real.sqrt C / ((3:ℝ)^(3*k)/e^2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (cutoff_denominator_lower k he0)
    _ = Real.sqrt C * e^2/(3:ℝ)^k := by
      rw [show 3*k = 2*k+k by omega, pow_add]
      field_simp
    _ ≤ (k:ℝ)*e^2/(3:ℝ)^k := by gcongr

/-- The explicit Bourgain error budget, with integer M and the unchanged
paper threshold eta. The stronger denominator permits later floor-cutoff use. -/
theorem total_bound {k : ℕ} (hk : 5 ≤ k) {e C : ℝ}
    (he0 : 0 < e) (he1 : e ≤ 1) (hC0 : 0 ≤ C) (hC : C ≤ k) :
    (cutoff k e : ℝ)^k * (eta k e)^2 +
      2*C*(3:ℝ)^(2*k)*(tau k e)^(2/3:ℝ) +
      (3:ℝ)^(2*k)*Real.sqrt C/(Real.sqrt (cutoff k e : ℝ)*tau k e) ≤
        e^2/(2*(k:ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hexp : 8*(k:ℝ)^2 ≤ (3:ℝ)^k := by exact_mod_cast three_pow_ge_eight_sq hk
  have hpoly : 2*(k:ℝ)*(1+3*(k:ℝ)) ≤ (3:ℝ)^k := by
    nlinarith [sq_nonneg ((k:ℝ)-1)]
  calc
    _ ≤ e^2/(3:ℝ)^k + 2*(k:ℝ)*e^2/(3:ℝ)^k + (k:ℝ)*e^2/(3:ℝ)^k :=
      add_le_add (add_le_add (first_term_le hk1 he0 he1) (middle_term_le he0.le hC0 hC))
        (third_term_le hk1 he0 hC)
    _ = ((1+3*(k:ℝ))*e^2)/(3:ℝ)^k := by ring
    _ ≤ e^2/(2*(k:ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h := mul_le_mul_of_nonneg_right hpoly (sq_nonneg e)
      nlinarith

end NarrowDNF.BourgainParameters
