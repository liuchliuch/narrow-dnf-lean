import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace NarrowDNF.ResidualGram
open scoped BigOperators
variable {Ω α : Type*} [Fintype Ω] [DecidableEq α]

def inner (w f g : Ω → ℝ) : ℝ := ∑ x, w x * f x * g x

theorem inner_comm (w f g : Ω → ℝ) : inner w f g = inner w g f := by
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem inner_sub_sub (w f g h j : Ω → ℝ) :
    inner w (fun x => f x-g x) (fun x => h x-j x) =
      inner w f h - inner w f j - inner w g h + inner w g j := by
  unfold inner
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

omit [DecidableEq α] in
theorem weighted_square_sum (w : Ω → ℝ) (A : Finset α) (v : α → Ω → ℝ) :
    (∑ x, w x * (∑ i ∈ A, v i x)^2) = ∑ i ∈ A, ∑ j ∈ A, inner w (v i) (v j) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Exact diagonal/offdiagonal expansion when the original components are
pairwise orthogonal and each original component is orthogonal to the other
components' approximations. All remaining offdiagonal terms are products of
the approximations themselves, as used for equal-rank Hatami components. -/
theorem residual_square_sum (w : Ω → ℝ) (A : Finset α) (f g : α → Ω → ℝ)
    (hff : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → inner w (f i) (f j) = 0)
    (hfg : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → inner w (f i) (g j) = 0) :
    (∑ x, w x * (∑ i ∈ A, (f i x-g i x))^2) =
      (∑ i ∈ A, ∑ x, w x * (f i x-g i x)^2) +
      ∑ i ∈ A, ∑ j ∈ A.erase i, inner w (g i) (g j) := by
  rw [weighted_square_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.add_sum_erase A _ hi]
  congr 1
  · unfold inner
    apply Finset.sum_congr rfl
    intro x _
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hji, hjA⟩ := Finset.mem_erase.mp hj
    rw [inner_sub_sub, hff i hi j hjA (Ne.symm hji), hfg i hi j hjA (Ne.symm hji),
      inner_comm w (g i) (f j), hfg j hjA i hi hji]
    ring

end NarrowDNF.ResidualGram
