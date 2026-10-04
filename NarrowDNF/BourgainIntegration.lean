import NarrowDNF.BourgainComponents
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr

noncomputable section
namespace NarrowDNF.BourgainIntegration
open BourgainComponents
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The low square-function part is bounded by its 2/3 moment. -/
theorem small_square_le (q τ : ℝ) (hq : 0 ≤ q) (hτ : 0 < τ) :
    (if q ≤ τ^2 then q else 0) ≤ τ^(2/3:ℝ) * q^(2/3:ℝ) := by
  by_cases hsmall : q ≤ τ^2
  · rw [if_pos hsmall]
    by_cases hq0 : q = 0
    · simp [hq0]
    have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hr := Real.rpow_le_rpow hq hsmall (by norm_num : (0:ℝ) ≤ 1/3)
    have heq : (τ^2)^(1/3:ℝ) = τ^(2/3:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
      norm_num
    rw [heq] at hr
    have hm := mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hq (2/3:ℝ))
    have hprod : q^(1/3:ℝ)*q^(2/3:ℝ)=q := by
      rw [← Real.rpow_add hqp]
      norm_num
    simpa only [hprod] using hm
  · simp only [if_neg hsmall]
    positivity

variable {α : Type*} [Fintype α]

/-- Weighted finite Cauchy–Schwarz for a nonnegative event-restricted observable. -/
theorem event_cauchy (w F : α → ℝ) (hw : ∀ x, 0 ≤ w x) (_hF : ∀ x, 0 ≤ F x)
    (B : α → Prop) [DecidablePred B] :
    (∑ x, w x * (if B x then F x else 0)) ≤
      Real.sqrt (∑ x, w x * F x^2) * Real.sqrt (∑ x, w x * (if B x then 1 else 0)) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset α)
    (r := fun x => w x * (if B x then F x else 0))
    (f := fun x => w x * F x^2)
    (g := fun x => w x * (if B x then 1 else 0))
    (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    (fun x _ => by by_cases hx : B x <;> simp [hx, hw x])
    (fun x _ => by by_cases hx : B x <;> simp [hx]; ring)
  have h2 : 0 ≤ ∑ x, w x * F x^2 := Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)
  have hb : 0 ≤ ∑ x, w x * (if B x then 1 else 0) := by
    apply Finset.sum_nonneg
    intro x _
    split <;> simp_all
  have hroot := Real.sqrt_mul h2 (∑ x, w x * (if B x then 1 else 0))
  rw [← hroot]
  exact Real.le_sqrt_of_sq_le hcs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Markov's inequality for the number of large square-function coordinates. -/
theorem large_event_probability_le (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (F : Finset (Finset ι)) (c : α → Finset ι → ℝ) (M : ℕ) (hM : 0 < M)
    (τ : ℝ) (hτ : 0 < τ) :
    (∑ x, w x * (if M ≤ (largeCoordinates F (c x) τ).card then 1 else 0)) ≤
      (∑ x, w x * ∑ i, coordinateSquare F (c x) i) / ((M : ℝ)*τ^2) := by
  have hd : (0:ℝ) < (M:ℝ)*τ^2 := mul_pos (Nat.cast_pos.mpr hM) (sq_pos_of_pos hτ)
  apply (le_div_iff₀ hd).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : M ≤ (largeCoordinates F (c x) τ).card
  · simp only [if_pos hx, mul_one]
    apply mul_le_mul_of_nonneg_left _ (hw x)
    have hcast : (M : ℝ) ≤ (largeCoordinates F (c x) τ).card := by exact_mod_cast hx
    have hcount := largeCoordinates_count_le F (c x) τ
    nlinarith [sq_nonneg τ]
  · simp only [if_neg hx, mul_zero, zero_mul]
    exact mul_nonneg (hw x) (Finset.sum_nonneg fun i _ => coordinateSquare_nonneg F (c x) i)


/-- The integrated three-piece Bourgain estimate, with every probability and
Cauchy–Schwarz/Markov step proved for the explicit finite weights. -/
theorem integrated_bourgain_split (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∑ x, w x = 1) (F : Finset (Finset ι)) (c : α → Finset ι → ℝ)
    (k M : ℕ) (hF : ∀ S ∈ F, S.card ≤ k) (hM : 0 < M)
    (η τ : ℝ) (hτ : 0 < τ) :
    (∑ x, w x * truncatedMass F (c x) η) ≤
      (M:ℝ)^k * η^2 + τ^(2/3:ℝ) *
        (∑ i, ∑ x, w x * (coordinateSquare F (c x) i)^(2/3:ℝ)) +
      Real.sqrt (∑ x, w x * (∑ S ∈ F, c x S^2)^2) *
        Real.sqrt (∑ x, w x * ∑ i, coordinateSquare F (c x) i) /
          (Real.sqrt (M:ℝ) * τ) := by
  let small := fun x => ∑ i, if coordinateSquare F (c x) i ≤ τ^2 then coordinateSquare F (c x) i else 0
  let total := fun x => ∑ S ∈ F, c x S^2
  let bad := fun x => M ≤ (largeCoordinates F (c x) τ).card
  have hsmall : (∑ x, w x * small x) ≤ τ^(2/3:ℝ) *
      (∑ i, ∑ x, w x * (coordinateSquare F (c x) i)^(2/3:ℝ)) := by
    calc
      _ ≤ ∑ x, w x * ∑ i, τ^(2/3:ℝ) * (coordinateSquare F (c x) i)^(2/3:ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (hw x)
        apply Finset.sum_le_sum
        intro i _
        exact small_square_le _ _ (coordinateSquare_nonneg F (c x) i) hτ
      _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hprob := large_event_probability_le w hw F c M hM τ hτ
  have hroot : Real.sqrt (∑ x, w x * (if bad x then 1 else 0)) ≤
      Real.sqrt (∑ x, w x * ∑ i, coordinateSquare F (c x) i) /
        (Real.sqrt (M:ℝ)*τ) := by
    calc
      _ ≤ Real.sqrt ((∑ x, w x * ∑ i, coordinateSquare F (c x) i) / ((M:ℝ)*τ^2)) :=
        Real.sqrt_le_sqrt hprob
      _ = _ := by
        rw [Real.sqrt_div, Real.sqrt_mul (Nat.cast_nonneg M), Real.sqrt_sq_eq_abs, abs_of_pos hτ]
        exact Finset.sum_nonneg fun x _ => mul_nonneg (hw x)
          (Finset.sum_nonneg fun i _ => coordinateSquare_nonneg F (c x) i)
  have htail := (event_cauchy w total hw (fun x => Finset.sum_nonneg fun S _ => sq_nonneg _) bad).trans
    (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _))
  have hbase : (∑ x, w x * truncatedMass F (c x) η) ≤
      (M:ℝ)^k * η^2 + (∑ x, w x * small x) + (∑ x, w x * (if bad x then total x else 0)) := by
    calc
      _ ≤ ∑ x, w x * ((M:ℝ)^k*η^2 + small x + (if bad x then total x else 0)) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (pointwise_bourgain_split F (c x) k M hF η τ) (hw x)
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul]
  calc
    _ ≤ (M:ℝ)^k * η^2 + (∑ x, w x * small x) + (∑ x, w x * (if bad x then total x else 0)) := hbase
    _ ≤ _ := by
      have := add_le_add (add_le_add_left hsmall ((M:ℝ)^k * η^2)) htail
      simpa only [total, mul_div_assoc] using this

end NarrowDNF.BourgainIntegration
