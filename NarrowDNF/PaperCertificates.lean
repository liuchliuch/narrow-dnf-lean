import NarrowDNF.CertificateBounds
import NarrowDNF.ProductMeasure

namespace NarrowDNF
namespace Activation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lemma 4.1 of arXiv:2609.00240v1, including its exact explicit DNF,
pointwise domination and both probability bounds. The closed bias interval
strengthens the paper's ambient interior-bias convention. -/
theorem certificates_and_truncation {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : ℕ) :
    (∀ x, u x = true → ∀ y, TermHolds (J.certificate x) y → u y = true) ∧
    (∀ T ∈ J.truncatedTerms u w, T.card ≤ w) ∧
    Monotone (J.truncatedDNF u w) ∧
    J.truncatedDNF u w ≤ u ∧
    ProductMeasure.error p u (J.truncatedDNF u w) ≤
      ProductMeasure.probability p (fun x => w < (J.certificate x).card) ∧
    ProductMeasure.probability p (fun x => w < (J.certificate x).card) ≤
      ProductMeasure.expectation p (fun x => ((J.activeFinset x).card : ℝ)) / (w + 1 : ℝ) := by
  refine ⟨?_, ?_, truncatedDNF_monotone J u w, truncatedDNF_le hJ hu hm w, ?_⟩
  · intro x hx y hy
    exact certificate_forces hJ hu hm hx hy
  · intro T hT
    exact truncatedTerms_width J u w hT
  · exact truncatedDNF_error_bound hJ hu hm w (ProductMeasure.weight p)
      (ProductMeasure.weight_nonneg hp0 hp1)

end Activation
end NarrowDNF
