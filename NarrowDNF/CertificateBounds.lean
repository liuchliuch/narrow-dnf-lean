import NarrowDNF.Certificates
import NarrowDNF.Weighted

namespace NarrowDNF
namespace Activation
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def truncatedDNF (J : Activation ι) (u : Cube ι → Bool)
    (w : ℕ) (x : Cube ι) : Bool := by
  classical exact decide (DNFHolds (J.truncatedTerms u w) x)

@[simp] theorem truncatedDNF_eq_true (J : Activation ι) (u : Cube ι → Bool)
    (w : ℕ) (x : Cube ι) :
    J.truncatedDNF u w x = true ↔ DNFHolds (J.truncatedTerms u w) x := by
  classical simp [truncatedDNF]

theorem truncatedDNF_monotone (J : Activation ι) (u : Cube ι → Bool) (w : ℕ) :
    Monotone (J.truncatedDNF u w) := by
  intro x y hxy
  cases hx : J.truncatedDNF u w x
  · exact Bool.false_le _
  · have hy := dnfHolds_mono (J.truncatedTerms u w) hxy
      ((truncatedDNF_eq_true J u w x).mp hx)
    rw [(truncatedDNF_eq_true J u w y).mpr hy]

theorem truncatedDNF_le {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ) :
    J.truncatedDNF u w ≤ u := by
  intro x
  cases hx : J.truncatedDNF u w x
  · exact Bool.false_le _
  · rw [truncatedTerms_sound hJ hu hm w ((truncatedDNF_eq_true J u w x).mp hx)]

theorem truncatedDNF_disagreement_large {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ)
    {x : Cube ι} (hx : u x ≠ J.truncatedDNF u w x) :
    w < (J.certificate x).card := by
  have hle := truncatedDNF_le hJ hu hm w x
  cases hux : u x <;> cases hg : J.truncatedDNF u w x
  · exact False.elim (hx (hux.trans hg.symm))
  · rw [hux, hg] at hle
    exact False.elim ((by decide : ¬(true ≤ false)) hle)
  · apply truncatedTerms_missed_large hux
    intro h
    have := (truncatedDNF_eq_true J u w x).mpr h
    simp [hg] at this
  · exact False.elim (hx (hux.trans hg.symm))

/-- The full two-stage inequality of Lemma 4.1, valid under every nonnegative
finite weighting (and therefore every Bernoulli product probability). -/
theorem truncatedDNF_error_bound {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ)
    (weights : Cube ι → ℝ) (hw : ∀ x, 0 ≤ weights x) :
    (∑ x, weights x * (if u x ≠ J.truncatedDNF u w x then 1 else 0)) ≤
      (∑ x, weights x * (if w < (J.certificate x).card then 1 else 0)) ∧
    (∑ x, weights x * (if w < (J.certificate x).card then 1 else 0)) ≤
      (∑ x, weights x * ((J.activeFinset x).card : ℝ)) / (w + 1 : ℝ) := by
  classical
  constructor
  · apply Finset.sum_le_sum
    intro x _
    by_cases h : u x ≠ J.truncatedDNF u w x
    · simp [h, truncatedDNF_disagreement_large hJ hu hm w h]
    · simp only [if_neg h, mul_zero]
      split <;> simp_all
  · apply (Weighted.integer_markov weights hw (fun x => (J.certificate x).card) w).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hw x)
    exact_mod_cast certificate_card_le J x

end Activation
end NarrowDNF
