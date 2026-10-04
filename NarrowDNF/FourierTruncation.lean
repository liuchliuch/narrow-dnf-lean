import NarrowDNF.Fourier
import NarrowDNF.ConditionalExpectation
import NarrowDNF.HatamiActivation

noncomputable section
namespace NarrowDNF.FourierTruncation
open ProductMeasure Fourier
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def partialSum (p : ℝ) (f : Cube ι → ℝ) (retained : Finset (Finset ι)) (x : Cube ι) : ℝ :=
  ∑ S ∈ retained, component p f S x

theorem expectation_finset_sum {α : Type*} (p : ℝ) (s : Finset α) (F : α → Cube ι → ℝ) :
    expectation p (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, expectation p (F i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem setCoefficient_sub (p : ℝ) (f g : Cube ι → ℝ) (S : Finset ι) :
    setCoefficient p (fun x => f x - g x) S = setCoefficient p f S - setCoefficient p g S := by
  unfold setCoefficient coefficient
  simp only [sub_mul]
  exact Fourier.expectation_sub p _ _

theorem component_coefficient {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (S T : Finset ι) :
    setCoefficient p (component p f S) T = if S = T then setCoefficient p f S else 0 := by
  unfold setCoefficient coefficient component setCharacter
  simp only [mul_assoc, expectation_const_mul]
  rw [orthogonality hp0 hp1]
  simp [setCoefficient, coefficient]

theorem setCoefficient_partialSum {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (retained : Finset (Finset ι)) (T : Finset ι) :
    setCoefficient p (partialSum p f retained) T = if T ∈ retained then setCoefficient p f T else 0 := by
  classical
  unfold partialSum setCoefficient coefficient
  simp only [Finset.sum_mul]
  rw [expectation_finset_sum]
  have h : ∀ S, expectation p (fun x => component p f S x * character p (maskEquivFinset.symm T) x) =
      if S = T then setCoefficient p f S else 0 := fun S => component_coefficient hp0 hp1 f S T
  simp_rw [h]
  simp [setCoefficient, coefficient]

/-- Exact finite Parseval remainder for an arbitrary retained Fourier family. -/
theorem squaredError_partialSum {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (retained : Finset (Finset ι)) :
    ConditionalExpectation.squaredError (weight p) f (partialSum p f retained) =
      ∑ S ∈ Finset.univ \ retained, setCoefficient p f S ^ 2 := by
  classical
  change expectation p (fun x => (f x - partialSum p f retained x)^2) = _
  rw [parseval_finset hp0 hp1]
  simp_rw [setCoefficient_sub, setCoefficient_partialSum hp0 hp1]
  rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S ∈ retained <;> simp [hS]


/-- The small-component energy with the paper's real degree cutoff. -/
def smallMassReal (p : ℝ) (f : Cube ι → ℝ) (k η : ℝ) : ℝ :=
  ∑ S : Finset ι, expectation p (fun x =>
    if (S.card : ℝ) ≤ k ∧ |component p f S x| ≤ η then component p f S x ^ 2 else 0)

/-- The elementary combination of Hatami's Steps I and II, before inserting
the separate high-degree and Bourgain bounds. -/
theorem significant_remainder_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (k η : ℝ) :
    ConditionalExpectation.squaredError (weight p) f
      (partialSum p f (HatamiActivation.significantSets p f k η)) ≤
      (∑ S : Finset ι, if k < (S.card : ℝ) then setCoefficient p f S ^ 2 else 0) +
        smallMassReal p f k η := by
  classical
  rw [squaredError_partialSum hp0 hp1, Finset.sdiff_eq_filter, Finset.sum_filter]
  unfold smallMassReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  by_cases hdeg : (S.card : ℝ) ≤ k
  · simp only [not_lt.mpr hdeg, if_false, zero_add]
    by_cases hS : S ∈ HatamiActivation.significantSets p f k η
    · simp only [hS, not_true_eq_false, if_false]
      apply expectation_nonneg hp0.le hp1.le
      intro x
      split <;> positivity
    · have hsmall : ∀ x, |component p f S x| ≤ η := by
        intro x
        by_contra hx
        apply hS
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ S, hdeg, x, lt_of_not_ge hx⟩
      simp only [hS, not_false_eq_true, if_true, hdeg, hsmall, and_self]
      rw [component_sq_mean hp0 hp1]
  · have hS : S ∉ HatamiActivation.significantSets p f k η := by
      intro h
      exact hdeg (Finset.mem_filter.mp h).2.1
    simp [hS, lt_of_not_ge hdeg, hdeg]

end NarrowDNF.FourierTruncation
