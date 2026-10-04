import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Finite fourth-moment duality

Weighted Hölder and finite self-adjoint operator duality used by the Bourgain
square-function proof. Every weight is explicit; zero weights are allowed.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainDuality

variable {α : Type*} [Fintype α]

/-- Weighted L(4/3) moment; using a moment instead of a norm keeps the final
contraction statement free of extraneous outer fractional powers. -/
def moment43 (w f : α → ℝ) : ℝ := ∑ x, w x * |f x| ^ (4/3 : ℝ)

theorem moment43_nonneg (w f : α → ℝ) (hw : ∀ x, 0 ≤ w x) : 0 ≤ moment43 w f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (Real.rpow_nonneg (abs_nonneg _) _)

/-- Weighted Hölder, with exponents 4/3 and 4. -/
theorem weighted_holder43 (w f g : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    |∑ x, w x * f x * g x| ≤
      moment43 w f ^ (3/4 : ℝ) * (∑ x, w x * g x ^ 4) ^ (1/4 : ℝ) := by
  have hc : Real.HolderConjugate (4/3) 4 := by
    constructor <;> norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hc
    (f := fun x => w x ^ (3/4 : ℝ) * |f x|)
    (g := fun x => w x ^ (1/4 : ℝ) * |g x|)
    (fun x _ => mul_nonneg (Real.rpow_nonneg (hw x) _) (abs_nonneg _))
    (fun x _ => mul_nonneg (Real.rpow_nonneg (hw x) _) (abs_nonneg _))
  have hweight (x : α) : w x ^ (3/4 : ℝ) * w x ^ (1/4 : ℝ) = w x := by
    rw [← Real.rpow_add' (hw x) (by norm_num : (3/4 : ℝ)+(1/4 : ℝ) ≠ 0)]
    norm_num
  have hf (x : α) : (w x ^ (3/4 : ℝ) * |f x|) ^ (4/3 : ℝ) =
      w x * |f x| ^ (4/3 : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw x) _) (abs_nonneg _),
      ← Real.rpow_mul (hw x)]
    norm_num
  have hg (x : α) : (w x ^ (1/4 : ℝ) * |g x|) ^ (4 : ℝ) = w x * g x ^ 4 := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw x) _) (abs_nonneg _),
      ← Real.rpow_mul (hw x)]
    norm_num
    simp [← abs_pow, abs_of_nonneg (show 0 ≤ g x ^ 4 by positivity)]
  have hprod (x : α) : (w x ^ (3/4 : ℝ) * |f x|) *
      (w x ^ (1/4 : ℝ) * |g x|) = w x * |f x| * |g x| := by
    calc
      _ = (w x ^ (3/4 : ℝ) * w x ^ (1/4 : ℝ)) * |f x| * |g x| := by ring
      _ = _ := by rw [hweight]
  simp only [hf, hg, hprod] at h
  norm_num only at h
  calc
    _ ≤ ∑ x, |w x * f x * g x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, w x * |f x| * |g x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_mul, abs_of_nonneg (hw x)]
    _ ≤ _ := h

/-- The fourth-power form of Hölder avoids fractional powers in operator
contraction and cancellation arguments. -/
theorem weighted_holder43_fourth (w f g : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x * f x * g x)^4 ≤ moment43 w f ^ 3 * ∑ x, w x * g x ^ 4 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (weighted_holder43 w f g hw) 4
  have hf0 := moment43_nonneg w f hw
  have hg0 : 0 ≤ ∑ x, w x * g x ^ 4 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (by positivity)
  rw [← abs_pow, abs_of_nonneg (by positivity), mul_pow,
    ← Real.rpow_mul_natCast hf0, ← Real.rpow_mul_natCast hg0] at h
  norm_num at h
  exact h

/-- The pointwise extremizer for L(4/3)-L4 duality. -/
def dual43 (t : ℝ) : ℝ := if 0 ≤ t then |t| ^ (1/3 : ℝ) else -|t| ^ (1/3 : ℝ)

theorem dual43_pair (t : ℝ) : t * dual43 t = |t| ^ (4/3 : ℝ) := by
  have h : |t| * |t| ^ (1/3 : ℝ) = |t| ^ (4/3 : ℝ) := by
    calc
      _ = |t| ^ (1 : ℝ) * |t| ^ (1/3 : ℝ) := by rw [Real.rpow_one]
      _ = |t| ^ ((1 : ℝ) + 1/3) :=
        (Real.rpow_add' (abs_nonneg t) (by norm_num)).symm
      _ = _ := by norm_num
  by_cases ht : 0 ≤ t
  · simpa [dual43, ht, abs_of_nonneg ht] using h
  · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    simp only [dual43, if_neg ht]
    simpa only [abs_of_nonpos ht', neg_mul, mul_neg, neg_neg] using h

theorem dual43_fourth (t : ℝ) : dual43 t ^ 4 = |t| ^ (4/3 : ℝ) := by
  unfold dual43
  split_ifs
  · rw [← Real.rpow_mul_natCast (abs_nonneg t)]
    norm_num
  · rw [neg_pow]
    norm_num only
    rw [← Real.rpow_mul_natCast (abs_nonneg t)]
    norm_num

/-- L4 contraction of a self-adjoint finite operator implies L(4/3) contraction.
No dual norm theorem or infinite-dimensional functional analysis is assumed. -/
theorem dual_fourth_contraction (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (T : (α → ℝ) → α → ℝ)
    (hself : ∀ f g, (∑ x, w x * T f x * g x) = ∑ x, w x * f x * T g x)
    (hfourth : ∀ f, (∑ x, w x * T f x ^ 4) ≤ ∑ x, w x * f x ^ 4)
    (f : α → ℝ) : moment43 w (T f) ≤ moment43 w f := by
  let g := fun x => dual43 (T f x)
  let L := moment43 w (T f)
  have hL0 : 0 ≤ L := moment43_nonneg _ _ hw
  have hA0 := moment43_nonneg w f hw
  have hpair : (∑ x, w x * T f x * g x) = L := by
    simp only [g, L, moment43, mul_assoc, dual43_pair]
  have hg : (∑ x, w x * g x ^ 4) = L := by
    simp only [g, L, moment43, dual43_fourth]
  have h := weighted_holder43_fourth w f (T g) hw
  rw [← hself f g, hpair] at h
  have hTg := hfourth g
  rw [hg] at hTg
  have hbound : L ^ 4 ≤ moment43 w f ^ 3 * L :=
    h.trans (mul_le_mul_of_nonneg_left hTg (pow_nonneg hA0 _))
  by_cases hL : L = 0
  · simpa only [← hL] using hA0
  · have hLp : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
    have hcube : L ^ 3 ≤ moment43 w f ^ 3 := by
      apply (mul_le_mul_iff_left₀ hLp).mp
      nlinarith [hbound]
    exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) hA0 hcube

/-- Dual form of an L2-to-L4 contraction, in polynomial moment form. -/
theorem dual_contract24 (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (T : (α → ℝ) → α → ℝ)
    (hself : ∀ f g, (∑ x, w x * T f x * g x) = ∑ x, w x * f x * T g x)
    (h24 : ∀ f, (∑ x, w x * T f x ^ 4) ≤ (∑ x, w x * f x ^ 2)^2)
    (f : α → ℝ) :
    (∑ x, w x * T f x ^ 2)^2 ≤ moment43 w f ^ 3 := by
  let L := ∑ x, w x * T f x ^ 2
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)
  have hA0 := moment43_nonneg w f hw
  have hpair : (∑ x, w x * T f x * T f x) = L := by
    simp only [L, pow_two, mul_assoc]
  have h := weighted_holder43_fourth w f (T (T f)) hw
  rw [← hself f (T f), hpair] at h
  have hbound : L ^ 4 ≤ moment43 w f ^ 3 * L^2 :=
    h.trans (mul_le_mul_of_nonneg_left (h24 (T f)) (pow_nonneg hA0 _))
  by_cases hL : L = 0
  · change L^2 ≤ _
    rw [hL]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using pow_nonneg hA0 3
  · have hLp : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hLp)).mp
    nlinarith [hbound]

end NarrowDNF.BourgainDuality
