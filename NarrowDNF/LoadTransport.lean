import NarrowDNF.AdaptiveShift
import NarrowDNF.ProductMeasure
import NarrowDNF.ActivationLoad
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-!
# Load transport under random forcing

Point-mass and expectation bounds at effective bias `2*p-p^2`. Bounds are stated
without division by point masses, so they hold also for degenerate biases.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem forced_bias_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ 2 * p - p ^ 2 := by
  nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]

theorem forced_bias_le_one (p : ℝ) : 2 * p - p ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg (1-p)]

theorem bitWeight_forcing_le {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    bitWeight (2 * p - p ^ 2) b ≤ (2 - p) * bitWeight p b := by
  cases b <;> simp only [bitWeight_false, bitWeight_true] <;> nlinarith

omit [DecidableEq ι] in
/-- The likelihood-ratio bound on an arbitrary finite cube, in multiplication
form. Applied to an activation's indexing set, the exponent is its arity. -/
theorem weight_forcing_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    weight (2 * p - p ^ 2) x ≤ (2 - p) ^ Fintype.card ι * weight p x := by
  unfold weight
  calc
    (∏ i, bitWeight (2 * p - p ^ 2) (x i)) ≤
        ∏ i, ((2-p) * bitWeight p (x i)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact bitWeight_nonneg (forced_bias_nonneg hp0 hp1) (forced_bias_le_one p) (x i)
      · intro i _
        exact bitWeight_forcing_le hp0 hp1 (x i)
    _ = (2-p) ^ Fintype.card ι * ∏ i, bitWeight p (x i) := by
      rw [Finset.prod_mul_distrib]
      simp

theorem expectation_forcing_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : (ι → Bool) → ℝ) (hF : ∀ x, 0 ≤ F x) :
    expectation (2 * p - p ^ 2) F ≤ (2 - p) ^ Fintype.card ι * expectation p F := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  calc
    weight (2 * p - p ^ 2) x * F x ≤
        ((2-p) ^ Fintype.card ι * weight p x) * F x :=
      mul_le_mul_of_nonneg_right (weight_forcing_le hp0 hp1 x) (hF x)
    _ = (2-p) ^ Fintype.card ι * (weight p x * F x) := mul_assoc _ _ _

end NarrowDNF.ProductMeasure

namespace NarrowDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def forcingCoordinates (d : Cube ι) : Finset ι :=
  Finset.univ.filter fun i => d i = true

theorem forceInput_forcingCoordinates (d x : Cube ι) :
    forceInput (forcingCoordinates d) x = fun i => x i || d i := by
  funext i
  cases hdi : d i <;> simp [forceInput, forcingCoordinates, hdi]

namespace Activation

open ProductMeasure
attribute [local instance] Classical.propDecidable

/-- Extend a local input by zero; locality makes this particular extension
irrelevant to the activation's value. -/
def extendLocal (S : Finset ι) (z : S → Bool) : Cube ι :=
  fun i => if hi : i ∈ S then z ⟨i, hi⟩ else false

theorem probability_restrict (J : Activation ι) (p : ℝ) (S : Finset ι) :
    probability p (J.fires S) =
      probability p (fun z : S → Bool => J.fires S (extendLocal S z)) := by
  unfold probability
  change (expectation p (fun x : Cube ι => if J.fires S x then 1 else 0)) =
    expectation p (fun z : S → Bool => if J.fires S (extendLocal S z) then 1 else 0)
  have h := expectation_local p (fun i => i ∈ S)
    (fun x => if J.fires S x then 1 else 0) (by
      intro x y hxy
      simp only [J.locality S x y hxy])
  convert h using 1
  congr 1
  exact Subsingleton.elim _ _

/-- An activation pays for its own indexing set, not the ambient dimension. -/
theorem probability_forcing_le (J : Activation ι) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) :
    probability (2*p-p^2) (J.fires S) ≤
      (2-p)^S.card * probability p (J.fires S) := by
  rw [probability_restrict J (2*p-p^2) S, probability_restrict J p S]
  simpa only [probability, Fintype.card_coe] using
    expectation_forcing_le hp0 hp1
      (fun z : S → Bool => if J.fires S (extendLocal S z) then (1 : ℝ) else 0)
      (by intro z; dsimp only; split <;> norm_num)

theorem load_forcing_le (J : Activation ι) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {d : ℕ} (hd : J.ArityLE d) :
    J.load (2*p-p^2) ≤ (2-p)^d * J.load p := by
  unfold load
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S.card ≤ d
  · have hpow : (2-p)^S.card ≤ (2-p)^d :=
      pow_le_pow_right₀ (by linarith) hS
    have hprob := probability_nonneg hp0 hp1 (J.fires S)
    calc
      (S.card : ℝ) * probability (2*p-p^2) (J.fires S) ≤
          (S.card : ℝ) * ((2-p)^S.card * probability p (J.fires S)) :=
        mul_le_mul_of_nonneg_left (probability_forcing_le J hp0 hp1 S) (by positivity)
      _ ≤ (S.card : ℝ) * ((2-p)^d * probability p (J.fires S)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hprob) (by positivity)
      _ = (2-p)^d * ((S.card : ℝ) * probability p (J.fires S)) := by ring
  · have hz : ∀ x, ¬ J.fires S x := hd S (Nat.lt_of_not_ge hS)
    simp [probability, hz]

/-- Exact mean activation probability after independent Bernoulli forcing. -/
theorem probability_forced_mean (J : Activation ι) (p : ℝ) (S : Finset ι) :
    expectation p (fun d : Cube ι =>
      probability p ((J.force (forcingCoordinates d)).fires S)) =
        probability (2*p-p^2) (J.fires S) := by
  unfold probability force
  simp only [forceInput_forcingCoordinates]
  rw [expectation_comm]
  exact forcing_expectation p (fun x => if J.fires S x then 1 else 0)

/-- The equality in Lemma 3.3, with a Bernoulli cube encoding the random set D. -/
theorem load_forced_mean (J : Activation ι) (p : ℝ) :
    expectation p (fun d : Cube ι => (J.force (forcingCoordinates d)).load p) =
      J.load (2*p-p^2) := by
  unfold load
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [expectation_const_mul, probability_forced_mean]

/-- The exact equality and both upper bounds of Lemma 3.3. -/
theorem load_transport (J : Activation ι) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {d : ℕ} (hd : J.ArityLE d) :
    expectation p (fun D : Cube ι => (J.force (forcingCoordinates D)).load p) =
      J.load (2*p-p^2) ∧
    J.load (2*p-p^2) ≤ (2-p)^d * J.load p ∧
    (2-p)^d * J.load p ≤ 2^d * J.load p := by
  refine ⟨load_forced_mean J p, load_forcing_le J hp0 hp1 hd, ?_⟩
  apply mul_le_mul_of_nonneg_right
  · exact pow_le_pow_left₀ (by linarith) (by linarith) d
  · unfold load
    exact Finset.sum_nonneg fun S _ =>
      mul_nonneg (by positivity) (probability_nonneg hp0 hp1 (J.fires S))

omit [Fintype ι] in
theorem force_arityLE {J : Activation ι} {d : ℕ} (hd : J.ArityLE d)
    (D : Finset ι) : (J.force D).ArityLE d := by
  intro S hS x
  exact hd S hS (forceInput D x)

/-- The active-union consequence at the end of Lemma 3.3. -/
theorem expected_forced_active_le (J : Activation ι) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {d : ℕ} (hd : J.ArityLE d) :
    expectation p (fun D : Cube ι => expectation p (fun x =>
      (((J.force (forcingCoordinates D)).activeFinset x).card : ℝ))) ≤
        (2-p)^d * J.load p := by
  apply (expectation_mono hp0 hp1 (fun D : Cube ι =>
    expected_active_le_load (J.force (forcingCoordinates D)) hp0 hp1)).trans
  rw [load_forced_mean]
  exact load_forcing_le J hp0 hp1 hd

end Activation
end NarrowDNF
