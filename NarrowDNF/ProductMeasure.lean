import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite Bernoulli product probability

The probability model is an explicit finite sum of product weights. Algebraic
identities hold for every real parameter; positivity claims state `0 ≤ p ≤ 1`.
No theorem here assumes a probability law or an analytic input without proof.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bernoulli mass of one bit. -/
def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

@[simp] theorem bitWeight_false (p : ℝ) : bitWeight p false = 1 - p := rfl
@[simp] theorem bitWeight_true (p : ℝ) : bitWeight p true = p := rfl

/-- Probability mass of a cube point. -/
def weight (p : ℝ) (x : ι → Bool) : ℝ := ∏ i, bitWeight p (x i)

/-- Expectation under the finite product weights. -/
def expectation (p : ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  ∑ x, weight p x * F x

/-- Probability of an arbitrary decidable predicate. -/
def probability (p : ℝ) (P : (ι → Bool) → Prop) [DecidablePred P] : ℝ :=
  expectation p (fun x => if P x then 1 else 0)

/-- Disagreement probability of two Boolean functions. -/
def error (p : ℝ) (f g : (ι → Bool) → Bool) : ℝ :=
  probability p (fun x => f x ≠ g x)

theorem bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitWeight p b := by
  cases b <;> simp only [bitWeight_false, bitWeight_true]
  · exact sub_nonneg.mpr hp1
  · exact hp0

omit [DecidableEq ι] in
theorem weight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ weight p x :=
  Finset.prod_nonneg fun i _ => bitWeight_nonneg hp0 hp1 (x i)

theorem bitWeight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    0 < bitWeight p b := by
  cases b <;> simp only [bitWeight_false, bitWeight_true]
  · exact sub_pos.mpr hp1
  · exact hp0

omit [DecidableEq ι] in
theorem weight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : ι → Bool) :
    0 < weight p x :=
  Finset.prod_pos fun i _ => bitWeight_pos hp0 hp1 (x i)

/-- Finite distributivity for independently chosen coordinates. -/
theorem sum_prod_coordinates {α : Type*} [Fintype α] (F : ι → α → ℝ) :
    (∑ x : ι → α, ∏ i, F i (x i)) = ∏ i, ∑ a, F i a := by
  classical
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α)) F).symm

@[simp] theorem sum_weight (p : ℝ) : ∑ x : ι → Bool, weight p x = 1 := by
  unfold weight
  rw [sum_prod_coordinates]
  simp

@[simp] theorem expectation_const (p c : ℝ) : expectation (ι := ι) p (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul]

@[simp] theorem expectation_zero (p : ℝ) : expectation (ι := ι) p (fun _ => 0) = 0 :=
  expectation_const p 0

@[simp] theorem expectation_one (p : ℝ) : expectation (ι := ι) p (fun _ => 1) = 1 :=
  expectation_const p 1

theorem expectation_add (p : ℝ) (F G : (ι → Bool) → ℝ) :
    expectation p (fun x => F x + G x) = expectation p F + expectation p G := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_mul_const (p c : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => F x * c) = expectation p F * c := by
  simp [expectation, mul_assoc, Finset.sum_mul]

theorem expectation_const_mul (p c : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => c * F x) = c * expectation p F := by
  simpa [mul_comm] using expectation_mul_const p c F

theorem expectation_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F : (ι → Bool) → ℝ} (hF : ∀ x, 0 ≤ F x) : 0 ≤ expectation p F :=
  Finset.sum_nonneg fun x _ => mul_nonneg (weight_nonneg hp0 hp1 x) (hF x)

theorem expectation_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : (ι → Bool) → ℝ} (hFG : ∀ x, F x ≤ G x) :
    expectation p F ≤ expectation p G :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hFG x) (weight_nonneg hp0 hp1 x)

theorem probability_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (ι → Bool) → Prop) [DecidablePred P] : 0 ≤ probability p P := by
  apply expectation_nonneg hp0 hp1
  intro x
  split_ifs <;> norm_num

theorem probability_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (ι → Bool) → Prop) [DecidablePred P] : probability p P ≤ 1 := by
  rw [← expectation_one (ι := ι) p]
  apply expectation_mono hp0 hp1
  intro x
  split_ifs <;> norm_num

theorem error_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f g : (ι → Bool) → Bool) : 0 ≤ error p f g :=
  probability_nonneg hp0 hp1 _

@[simp] theorem error_self (p : ℝ) (f : (ι → Bool) → Bool) : error p f f = 0 := by
  simp [error, probability]

theorem error_symm (p : ℝ) (f g : (ι → Bool) → Bool) : error p f g = error p g f := by
  simp only [error, probability, ne_comm]

theorem error_triangle {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f g h : (ι → Bool) → Bool) : error p f h ≤ error p f g + error p g h := by
  unfold error probability
  rw [← expectation_add]
  apply expectation_mono hp0 hp1
  intro x
  cases hfx : f x <;> cases hgx : g x <;> cases hhx : h x <;> simp [hfx, hgx, hhx]

/-- Split off the mass contributed by a chosen coordinate. -/
theorem weight_split (p : ℝ) (i : ι) (x : ι → Bool) :
    weight p x = bitWeight p (x i) * weight p (fun j : {j // j ≠ i} => x j) := by
  exact Fintype.prod_eq_mul_prod_subtype_ne (fun j => bitWeight p (x j)) i

/-- Insert a bit into the missing coordinate of a smaller cube. -/
def insertBit (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) : ι → Bool :=
  (Equiv.funSplitAt i Bool).symm (b,z)

omit [Fintype ι] in
@[simp] theorem insertBit_at (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    insertBit i b z i = b := by simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype ι] in
@[simp] theorem insertBit_away (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool)
    (j : {j // j ≠ i}) : insertBit i b z j = z j := by
  simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt, j.property]

/-- Fubini's formula for one Bernoulli coordinate and its complement. -/
theorem expectation_split (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) :
    expectation p F =
      (1-p) * expectation p (fun z => F (insertBit i false z)) +
        p * expectation p (fun z => F (insertBit i true z)) := by
  have h := Fintype.sum_equiv (Equiv.funSplitAt i Bool)
    (fun x => weight p x * F x)
    (fun t : Bool × ({j // j ≠ i} → Bool) =>
      bitWeight p t.1 * weight p t.2 * F (insertBit i t.1 t.2))
    (fun x => by
      have hin : insertBit i (x i) (fun j : {j // j ≠ i} => x j) = x :=
        (Equiv.funSplitAt i Bool).symm_apply_apply x
      change weight p x * F x = bitWeight p (x i) *
        weight p (fun j : {j // j ≠ i} => x j) * F (insertBit i (x i) (fun j => x j))
      rw [hin, weight_split p i x])
  unfold expectation
  rw [h, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [bitWeight_true, bitWeight_false, mul_assoc, ← Finset.mul_sum]
  exact add_comm _ _

/-- Independence factorization for observables that factor over coordinates. -/
theorem expectation_prod (p : ℝ) (F : ι → Bool → ℝ) :
    expectation p (fun x => ∏ i, F i (x i)) =
      ∏ i, ((1-p) * F i false + p * F i true) := by
  unfold expectation weight
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_prod_coordinates (fun i b => bitWeight p b * F i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [add_comm]

/-- Finite double-product distributivity used in the forcing law. -/
theorem sum_prod_two_coordinates (F : ι → Bool → Bool → ℝ) :
    (∑ x : ι → Bool, ∑ y : ι → Bool, ∏ i, F i (x i) (y i)) =
      ∏ i, ∑ a : Bool, ∑ b : Bool, F i a b := by
  classical
  let e : ((ι → Bool) × (ι → Bool)) ≃ (ι → Bool × Bool) :=
    { toFun := fun t i => (t.1 i, t.2 i)
      invFun := fun z => (fun i => (z i).1, fun i => (z i).2)
      left_inv := by intro t; rfl
      right_inv := by intro z; rfl }
  rw [← Fintype.sum_prod_type' (fun (x y : ι → Bool) => ∏ i, F i (x i) (y i))]
  rw [Fintype.sum_equiv e
    (fun t => ∏ i, F i (t.1 i) (t.2 i))
    (fun z => ∏ i, F i (z i).1 (z i).2) (fun _ => rfl)]
  rw [sum_prod_coordinates (fun i (t : Bool × Bool) => F i t.1 t.2)]
  simp only [Fintype.sum_prod_type]

/-- Exact point masses of coordinatewise OR of two independent biased cubes.
The second cube is the random set of forced coordinates in Lemma 3.3. -/
theorem forcing_mass (p : ℝ) (z : ι → Bool) :
    (∑ x : ι → Bool, ∑ d : ι → Bool,
      if (fun i => x i || d i) = z then weight p x * weight p d else 0) =
        weight (2*p-p^2) z := by
  have hterm (x d : ι → Bool) :
      (if (fun i => x i || d i) = z then weight p x * weight p d else 0) =
        ∏ i, if (x i || d i) = z i then bitWeight p (x i) * bitWeight p (d i) else 0 := by
    rw [Fintype.prod_ite_zero, Finset.prod_mul_distrib]
    simp only [weight, funext_iff]
  simp_rw [hterm]
  rw [sum_prod_two_coordinates
    (fun i a b => if (a || b) = z i then bitWeight p a * bitWeight p b else 0)]
  apply Finset.prod_congr rfl
  intro i _
  cases z i <;> simp [bitWeight] <;> ring

/-- Change of variables for a finite weighted pushforward, including noninjective maps. -/
theorem weighted_pushforward {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (g : α → β) (F : β → ℝ) :
    (∑ a, w a * F (g a)) = ∑ b, (∑ a, if g a = b then w a else 0) * F b := by
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- The exact OR/forcing distribution law for every real-valued observable. -/
theorem forcing_expectation (p : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => expectation p (fun d => F (fun i => x i || d i))) =
      expectation (2*p-p^2) F := by
  unfold expectation
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [← Fintype.sum_prod_type'
    (fun (x d : ι → Bool) => weight p x * weight p d * F (fun i => x i || d i))]
  rw [weighted_pushforward
    (fun t : (ι → Bool) × (ι → Bool) => weight p t.1 * weight p t.2)
    (fun t : (ι → Bool) × (ι → Bool) => fun i => t.1 i || t.2 i) F]
  simp_rw [Fintype.sum_prod_type, forcing_mass]

/-- Interchange an expectation and a finite sum. -/
theorem expectation_sum {κ : Type*} [Fintype κ] (p : ℝ)
    (F : κ → (ι → Bool) → ℝ) :
    expectation p (fun x => ∑ a, F a x) = ∑ a, expectation p (F a) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Finite expectations with respect to independent cubes commute. -/
theorem expectation_comm (p q : ℝ) (F : (ι → Bool) → (ι → Bool) → ℝ) :
    expectation p (fun x => expectation q (F x)) =
      expectation q (fun y => expectation p (fun x => F x y)) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [DecidableEq ι] in
/-- Product weights factor over a coordinate predicate and its complement. -/
theorem weight_partition (p : ℝ) (P : ι → Prop) [DecidablePred P] (x : ι → Bool) :
    weight p x = weight p (fun i : {i // P i} => x i) *
      weight p (fun i : {i // ¬ P i} => x i) := by
  exact (Fintype.prod_subtype_mul_prod_subtype P (fun i => bitWeight p (x i))).symm

/-- The marginal on any chosen coordinates is the corresponding product law. -/
theorem expectation_restrict (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F : ({i // P i} → Bool) → ℝ) :
    expectation p (fun x : ι → Bool => F (fun i => x i)) = expectation p F := by
  let e := Equiv.piEquivPiSubtypeProd P (fun _ : ι => Bool)
  have h := Fintype.sum_equiv e
    (fun x => weight p x * F (fun i => x i))
    (fun t : ({i // P i} → Bool) × ({i // ¬ P i} → Bool) =>
      weight p t.1 * weight p t.2 * F t.1)
    (fun x => by dsimp only; rw [weight_partition p P x]; rfl)
  unfold expectation
  rw [h, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  calc
    (∑ z : {i // ¬ P i} → Bool, weight p y * weight p z * F y) =
        (∑ z : {i // ¬ P i} → Bool, weight p z) * (weight p y * F y) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = weight p y * F y := by rw [sum_weight, one_mul]

/-- Extend a partial cube input by zero outside its coordinate predicate. -/
def extendFalse (P : ι → Prop) [DecidablePred P] (z : {i // P i} → Bool) : ι → Bool :=
  fun i => if h : P i then z ⟨i,h⟩ else false

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem extendFalse_on (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) (i : {i // P i}) : extendFalse P z i = z i := by
  simp [extendFalse, i.property]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem extendFalse_off (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) (i : ι) (hi : ¬ P i) : extendFalse P z i = false := by
  simp [extendFalse, hi]

/-- A local observable may be integrated over only the coordinates it reads. -/
theorem expectation_local (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F : (ι → Bool) → ℝ)
    (hF : ∀ x y, (∀ i, P i → x i = y i) → F x = F y) :
    expectation p F = expectation p (fun z => F (extendFalse P z)) := by
  calc
    expectation p F =
        expectation p (fun x : ι → Bool => F (extendFalse P (fun i => x i))) := by
      apply congrArg (expectation p)
      funext x
      apply hF
      intro i hi
      simp [extendFalse, hi]
    _ = expectation p (fun z => F (extendFalse P z)) :=
      expectation_restrict p P (fun z => F (extendFalse P z))

end NarrowDNF.ProductMeasure
