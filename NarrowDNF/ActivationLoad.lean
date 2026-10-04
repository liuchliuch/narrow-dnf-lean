import NarrowDNF.Certificates
import NarrowDNF.ProductMeasure
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace NarrowDNF
namespace Activation
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def load (J : Activation ι) (p : ℝ) : ℝ := by
  classical exact ∑ S : Finset ι, (S.card : ℝ) * ProductMeasure.probability p (J.fires S)

def ArityLE (J : Activation ι) (d : ℕ) : Prop :=
  ∀ S, d < S.card → ∀ x, ¬ J.fires S x

theorem activeFinset_eq_biUnion (J : Activation ι) (x : Cube ι) :
    J.activeFinset x = (Finset.univ.filter fun S : Finset ι => J.fires S x).biUnion id := by
  classical
  ext i
  simp [active, and_comm]

theorem active_card_le_sum (J : Activation ι) (x : Cube ι) :
    ((J.activeFinset x).card : ℝ) ≤
      ∑ S : Finset ι, (S.card : ℝ) * (if J.fires S x then 1 else 0) := by
  classical
  rw [activeFinset_eq_biUnion]
  have h := Finset.card_biUnion_le (s := Finset.univ.filter fun S : Finset ι => J.fires S x)
    (t := id)
  have hr : (((Finset.univ.filter fun S : Finset ι => J.fires S x).biUnion id).card : ℝ) ≤
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => J.fires S x), (S.card : ℝ) := by
    exact_mod_cast h
  simpa [Finset.sum_filter, mul_ite] using hr

theorem expected_active_le_load (J : Activation ι) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProductMeasure.expectation p (fun x => ((J.activeFinset x).card : ℝ)) ≤ J.load p := by
  classical
  apply (ProductMeasure.expectation_mono hp0 hp1 (fun x => active_card_le_sum J x)).trans_eq
  simp only [ProductMeasure.expectation, load, ProductMeasure.probability, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro x _
  ring

end Activation
end NarrowDNF
