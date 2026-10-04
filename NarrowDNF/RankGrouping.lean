import NarrowDNF.ProductMeasure
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace NarrowDNF.RankGrouping
open scoped BigOperators

variable {α β : Type*} [DecidableEq β]

/-- A finite sum grouped by any rank map, with no multiplicity lost. -/
theorem sum_by_rank (A : Finset α) (R : Finset β) (rank : α → β)
    (hcover : ∀ i ∈ A, rank i ∈ R) (v : α → ℝ) :
    (∑ i ∈ A, v i) = ∑ r ∈ R, ∑ i ∈ A with rank i = r, v i := by
  exact (Finset.sum_fiberwise_of_maps_to hcover v).symm

/-- Rank-group Cauchy–Schwarz. Choosing ranks 1,...,k gives exactly factor k;
choosing ranks 0,...,k gives k+1. -/
theorem squared_sum_le_rank_groups (A : Finset α) (R : Finset β) (rank : α → β)
    (hcover : ∀ i ∈ A, rank i ∈ R) (v : α → ℝ) :
    (∑ i ∈ A, v i)^2 ≤ (R.card : ℝ) *
      ∑ r ∈ R, (∑ i ∈ A with rank i = r, v i)^2 := by
  rw [sum_by_rank A R rank hcover v]
  simpa using Finset.sum_mul_sq_le_sq_mul_sq R (fun _ => (1:ℝ))
    (fun r => ∑ i ∈ A with rank i = r, v i)

/-- The same rank-group inequality under arbitrary finite nonnegative weights. -/
theorem weighted_squared_sum_le_rank_groups {Ω : Type*} [Fintype Ω]
    (weights : Ω → ℝ) (hw : ∀ x, 0 ≤ weights x)
    (A : Finset α) (R : Finset β) (rank : α → β)
    (hcover : ∀ i ∈ A, rank i ∈ R) (v : Ω → α → ℝ) :
    (∑ x, weights x * (∑ i ∈ A, v x i)^2) ≤ (R.card : ℝ) *
      ∑ r ∈ R, ∑ x, weights x * (∑ i ∈ A with rank i = r, v x i)^2 := by
  calc
    _ ≤ ∑ x, weights x * ((R.card : ℝ) * ∑ r ∈ R, (∑ i ∈ A with rank i = r, v x i)^2) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
        (squared_sum_le_rank_groups A R rank hcover (v x)) (hw x)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro x _
      ring

end NarrowDNF.RankGrouping
