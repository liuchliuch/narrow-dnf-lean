import NarrowDNF.ProductMeasure
import NarrowDNF.Adaptive
import Mathlib.Tactic.FieldSimp

/-!
# Conditional expectation on a finite partition

A partition is represented by a map `φ : α → β`; each realized fiber has
positive mass when the input weights are strictly positive. This file derives
least-squares projection and Boolean threshold rounding from finite sums. It
does not assume Hatami's construction-specific residual bound.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ConditionalExpectation

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- Total weight of one partition atom. -/
def mass (φ : α → β) (w : α → ℝ) (b : β) : ℝ :=
  ∑ a : {a // φ a = b}, w a

/-- Weighted first moment on one partition atom. -/
def moment (φ : α → β) (w F : α → ℝ) (b : β) : ℝ :=
  ∑ a : {a // φ a = b}, w a * F a

/-- Atom mean. Unrealized atoms have value zero by the field's zero-division convention. -/
def mean (φ : α → β) (w F : α → ℝ) (b : β) : ℝ :=
  moment φ w F b / mass φ w b

/-- Conditional mean pulled back to the input space. -/
def conditional (φ : α → β) (w F : α → ℝ) (a : α) : ℝ :=
  mean φ w F (φ a)

omit [Fintype β] [DecidableEq β] in
/-- Conditional means are independent of the implementation of label equality. -/
theorem mean_decidableEq_irrel (d₁ d₂ : DecidableEq β) (φ : α → β) (w F : α → ℝ) (b : β) :
    @mean α β _ d₁ φ w F b = @mean α β _ d₂ φ w F b := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  rw [hd]

/-- Weighted squared error, without any implicit normalization. -/
def squaredError (w F G : α → ℝ) : ℝ := ∑ a, w a * (F a - G a)^2

/-- Numeric encoding of a Boolean value. -/
def value (b : Bool) : ℝ := if b then 1 else 0

/-- Weighted Boolean disagreement. -/
def booleanError (w : α → ℝ) (f g : α → Bool) : ℝ :=
  ∑ a, w a * (if f a = g a then 0 else 1)

/-- Strict half-threshold, matching the convention in Appendix A of the paper. -/
def threshold (m : ℝ) : Bool := decide ((1 / 2 : ℝ) < m)

def decoder (φ : α → β) (w : α → ℝ) (f : α → Bool) (a : α) : Bool :=
  threshold (conditional φ w (fun x => value (f x)) a)

omit [Fintype β] in
theorem mass_nonneg (φ : α → β) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (b : β) :
    0 ≤ mass φ w b := Finset.sum_nonneg fun a _ => hw a

omit [Fintype β] in
theorem mass_pos (φ : α → β) (w : α → ℝ) (hw : ∀ a, 0 < w a)
    (a : α) : 0 < mass φ w (φ a) := by
  have hle : w a ≤ mass φ w (φ a) := by
    unfold mass
    exact Finset.single_le_sum (f := fun y : {x // φ x = φ a} => w y)
      (fun y _ => (hw y).le) (Finset.mem_univ (⟨a,rfl⟩ : {x // φ x = φ a}))
  exact (hw a).trans_le hle

omit [Fintype β] in
/-- The mean satisfies its defining weighted first-moment equation on every atom,
including unrealized ones. -/
theorem mean_mul_mass (φ : α → β) (w F : α → ℝ) (hw : ∀ a, 0 < w a) (b : β) :
    mean φ w F b * mass φ w b = moment φ w F b := by
  by_cases hb : ∃ a, φ a = b
  · obtain ⟨a, rfl⟩ := hb
    exact div_mul_cancel₀ _ (mass_pos φ w hw a).ne'
  · haveI : IsEmpty {a // φ a = b} := ⟨fun a => hb ⟨a,a.property⟩⟩
    simp [mean, mass, moment]

omit [Fintype β] in
theorem conditional_eq_of_atom_eq (φ : α → β) (w F : α → ℝ)
    {a a' : α} (h : φ a = φ a') : conditional φ w F a = conditional φ w F a' := by
  simp only [conditional, h]

omit [Fintype β] in
theorem decoder_eq_of_atom_eq (φ : α → β) (w : α → ℝ) (f : α → Bool)
    {a a' : α} (h : φ a = φ a') : decoder φ w f a = decoder φ w f a' := by
  unfold decoder
  rw [conditional_eq_of_atom_eq φ w _ h]

/-- The residual has zero weighted inner product with every atom-constant function. -/
theorem residual_orthogonal (φ : α → β) (w F : α → ℝ) (hw : ∀ a, 0 < w a)
    (G : β → ℝ) :
    (∑ a, w a * (F a - conditional φ w F a) * G (φ a)) = 0 := by
  rw [← Fintype.sum_fiberwise φ]
  apply Finset.sum_eq_zero
  intro b _
  have h : ∀ a : {a // φ a = b}, conditional φ w F a = mean φ w F b := by
    intro a
    simp [conditional, a.property]
  simp_rw [h]
  calc
    (∑ a : {a // φ a = b}, w a * (F a - mean φ w F b) * G (φ a)) =
        (moment φ w F b - mean φ w F b * mass φ w b) * G b := by
      simp_rw [show ∀ a : {a // φ a = b}, φ a = b from fun a => a.property]
      unfold moment mass
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 0 := by rw [mean_mul_mass φ w F hw b]; ring

/-- Exact weighted Pythagorean identity for finite conditional expectation. -/
theorem squaredError_decomposition (φ : α → β) (w F : α → ℝ)
    (hw : ∀ a, 0 < w a) (G : β → ℝ) :
    squaredError w F (fun a => G (φ a)) =
      squaredError w F (conditional φ w F) +
        squaredError w (conditional φ w F) (fun a => G (φ a)) := by
  have horth := residual_orthogonal φ w F hw (fun b => mean φ w F b - G b)
  have hpoint (a : α) :
      w a * (F a - G (φ a))^2 =
        w a * (F a - conditional φ w F a)^2 +
          w a * (conditional φ w F a - G (φ a))^2 +
            2 * (w a * (F a - conditional φ w F a) *
              (mean φ w F (φ a) - G (φ a))) := by
    unfold conditional
    ring
  unfold squaredError
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [horth, mul_zero, add_zero]

/-- Conditional expectation is a least-squares projection onto atom readouts. -/
theorem squaredError_minimal (φ : α → β) (w F : α → ℝ)
    (hw : ∀ a, 0 < w a) (G : β → ℝ) :
    squaredError w F (conditional φ w F) ≤ squaredError w F (fun a => G (φ a)) := by
  rw [squaredError_decomposition φ w F hw G]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun a _ => mul_nonneg (hw a).le (sq_nonneg _))

/-- The pointwise factor-four Boolean rounding inequality; no range assumption
on the real approximator is necessary. -/
theorem threshold_error_le (b : Bool) (m : ℝ) :
    (if b = threshold m then (0:ℝ) else 1) ≤ 4 * (value b - m)^2 := by
  by_cases hm : (1/2:ℝ) < m
  · have ht : threshold m = true := by exact decide_eq_true hm
    cases b <;> rw [ht] <;> norm_num [value] <;> nlinarith [sq_nonneg (m-1/2)]
  · have hm' : m ≤ (1/2:ℝ) := le_of_not_gt hm
    have ht : threshold m = false := by exact decide_eq_false hm
    cases b <;> rw [ht] <;> norm_num [value] <;> nlinarith [sq_nonneg (m-1/2)]

omit [Fintype β] in
/-- Thresholding the conditional mean costs at most four times its squared residual. -/
theorem decoder_error_le_four (φ : α → β) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (f : α → Bool) :
    booleanError w f (decoder φ w f) ≤
      4 * squaredError w (fun a => value (f a)) (conditional φ w (fun a => value (f a))) := by
  unfold booleanError squaredError
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have h := mul_le_mul_of_nonneg_left
    (threshold_error_le (f a) (conditional φ w (fun a => value (f a)) a)) (hw a)
  simpa only [decoder, mul_left_comm] using h

omit [Fintype β] in
/-- Error of a constant Boolean decision on one atom, in terms of its
mass and acceptance moment. -/
theorem constant_error_on_atom (φ : α → β) (w : α → ℝ) (f : α → Bool)
    (b : β) (c : Bool) :
    (∑ a : {a // φ a = b}, w a * (if f a = c then 0 else 1)) =
      if c then mass φ w b - moment φ w (fun a => value (f a)) b
      else moment φ w (fun a => value (f a)) b := by
  cases c
  · unfold moment
    apply Finset.sum_congr rfl
    intro a _
    cases h : f a <;> simp_all [value]
  · unfold mass moment
    simp only [ite_true]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    cases h : f a <;> simp_all [value]

omit [Fintype β] in
/-- The half-threshold chooses a least-error decision on each individual atom. -/
theorem atom_threshold_optimal (φ : α → β) (w : α → ℝ) (hw : ∀ a, 0 < w a)
    (f : α → Bool) (b : β) (c : Bool) :
    (∑ a : {a // φ a = b}, w a *
      (if f a = threshold (mean φ w (fun a => value (f a)) b) then 0 else 1)) ≤
        ∑ a : {a // φ a = b}, w a * (if f a = c then 0 else 1) := by
  rw [constant_error_on_atom, constant_error_on_atom]
  have hM := mass_nonneg φ w (fun a => (hw a).le) b
  have hN := mean_mul_mass φ w (fun a => value (f a)) hw b
  by_cases hm : (1/2:ℝ) < mean φ w (fun a => value (f a)) b
  · have ht : threshold (mean φ w (fun a => value (f a)) b) = true := decide_eq_true hm
    have hp := mul_nonneg hM (show 0 ≤ mean φ w (fun a => value (f a)) b - 1/2 by linarith)
    cases c <;> simp only [ht, Bool.false_eq_true, ite_true, ite_false] <;>
      nlinarith
  · have ht : threshold (mean φ w (fun a => value (f a)) b) = false := decide_eq_false hm
    have hp := mul_nonneg hM (show 0 ≤ 1/2 - mean φ w (fun a => value (f a)) b by linarith)
    cases c <;> simp only [ht, Bool.false_eq_true, ite_true, ite_false] <;>
      nlinarith

/-- Bayes optimality: the threshold decoder has no larger disagreement than
any Boolean function of the same partition label. -/
theorem decoder_error_minimal (φ : α → β) (w : α → ℝ) (hw : ∀ a, 0 < w a)
    (f : α → Bool) (g : β → Bool) :
    booleanError w f (decoder φ w f) ≤ booleanError w f (fun a => g (φ a)) := by
  unfold booleanError
  rw [← Fintype.sum_fiberwise φ (fun a => w a * (if f a = decoder φ w f a then 0 else 1)),
    ← Fintype.sum_fiberwise φ (fun a => w a * (if f a = g (φ a) then 0 else 1))]
  apply Finset.sum_le_sum
  intro b _
  simp only [decoder, conditional]
  simp_rw [show ∀ a : {a // φ a = b}, φ a = b from fun a => a.property]
  exact atom_threshold_optimal φ w hw f b (g b)

omit [Fintype β] in
/-- A real function constant on partition fibers has a global readout map. -/
theorem exists_readout (φ : α → β) (G : α → ℝ)
    (hG : ∀ x y, φ x = φ y → G x = G y) :
    ∃ g : β → ℝ, ∀ x, G x = g (φ x) := by
  classical
  let g : β → ℝ := fun b => if h : ∃ a, φ a = b then G h.choose else 0
  refine ⟨g, ?_⟩
  intro x
  have h : ∃ a, φ a = φ x := ⟨x,rfl⟩
  simp only [g, dif_pos h]
  exact (hG h.choose x h.choose_spec).symm

/-- Least-squares optimality for any fiber-measurable function, without requiring
its readout map as an additional argument. -/
theorem squaredError_minimal_of_measurable (φ : α → β) (w F G : α → ℝ)
    (hw : ∀ a, 0 < w a) (hG : ∀ x y, φ x = φ y → G x = G y) :
    squaredError w F (conditional φ w F) ≤ squaredError w F G := by
  obtain ⟨g,hg⟩ := exists_readout φ G hG
  have heq : G = fun a => g (φ a) := funext hg
  rw [heq]
  exact squaredError_minimal φ w F hw g

section Adaptive
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite coding of an adaptive atom, with actual labels retained on its active union. -/
def adaptiveCode (J : Activation ι) (x : Cube ι) : Finset ι × Cube ι := by
  classical
  exact (Finset.univ.filter (fun i => i ∈ J.active x), J.zeroOutside x)

omit [DecidableEq ι] in
/-- The code induces exactly the adaptive partition, not a finer substitute. -/
theorem adaptiveCode_eq_iff (J : Activation ι) (x y : Cube ι) :
    adaptiveCode J x = adaptiveCode J y ↔ J.SameAtom x y := by
  classical
  constructor
  · intro h
    have hs := congrArg Prod.fst h
    have hA : J.active x = J.active y := by
      ext i
      have hi := congrArg (fun s : Finset ι => i ∈ s) hs
      simpa [adaptiveCode] using hi
    refine ⟨hA, ?_⟩
    intro i hi
    have hi' : i ∈ J.active y := hA ▸ hi
    have hl := congrArg (fun t : Finset ι × Cube ι => t.2 i) h
    simpa [adaptiveCode, Activation.zeroOutside, hi, hi'] using hl
  · rintro ⟨hA,hlabels⟩
    apply Prod.ext
    · apply Finset.ext
      intro i
      simp [adaptiveCode, hA]
    · funext i
      by_cases hi : i ∈ J.active x
      · have hi' : i ∈ J.active y := hA ▸ hi
        simp [adaptiveCode, Activation.zeroOutside, hi, hi', hlabels i hi]
      · have hi' : i ∉ J.active y := hA ▸ hi
        simp [adaptiveCode, Activation.zeroOutside, hi, hi']

/-- Conditional mean with respect to the actual adaptive atom partition. -/
def adaptiveMean (p : ℝ) (J : Activation ι) (f : Cube ι → Bool) : Cube ι → ℝ := by
  classical
  exact conditional (adaptiveCode J) (ProductMeasure.weight p) (fun x => value (f x))

/-- Threshold readout of the adaptive conditional mean. -/
def adaptiveDecoder (p : ℝ) (J : Activation ι) (f : Cube ι → Bool) : Cube ι → Bool :=
  fun x => threshold (adaptiveMean p J f x)

theorem adaptiveDecoder_measurable (p : ℝ) (J : Activation ι) (f : Cube ι → Bool) :
    J.Measurable (adaptiveDecoder p J f) := by
  classical
  intro x y hxy
  apply decoder_eq_of_atom_eq
  exact (adaptiveCode_eq_iff J x y).mpr hxy

/-- The final thresholding step of Appendix A, with the residual left explicit. -/
theorem adaptiveDecoder_error_le_four {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Activation ι) (f : Cube ι → Bool) :
    ProductMeasure.error p f (adaptiveDecoder p J f) ≤
      4 * ProductMeasure.expectation p (fun x => (value (f x) - adaptiveMean p J f x)^2) := by
  classical
  have h := decoder_error_le_four (adaptiveCode J) (ProductMeasure.weight p)
    (ProductMeasure.weight_nonneg hp0 hp1) f
  simpa [ProductMeasure.error, ProductMeasure.probability, ProductMeasure.expectation,
    booleanError, squaredError, adaptiveDecoder, adaptiveMean, decoder] using h

end Adaptive

section CoordinatePartition
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Combine assignments on complementary coordinate sets. -/
def merge (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) (y : {i // ¬ P i} → Bool) : Cube ι :=
  fun i => if h : P i then z ⟨i,h⟩ else y ⟨i,h⟩

/-- A fixed-coordinate fiber is exactly the cube on the complementary coordinates. -/
def restrictionFiberEquiv (P : ι → Prop) [DecidablePred P] (z : {i // P i} → Bool) :
    {x : Cube ι // (fun i : {i // P i} => x i) = z} ≃ ({i // ¬ P i} → Bool) where
  toFun x i := x.val i
  invFun y := ⟨merge P z y, by funext i; simp [merge, i.property]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : P i
    · have h := congrFun x.property (⟨i,hi⟩ : {i // P i})
      simpa [merge, hi] using h.symm
    · simp [merge, hi]
  right_inv y := by
    funext i
    simp [merge, i.property]

/-- Exact probability of a coordinate restriction. -/
theorem mass_restriction (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) :
    mass (fun x : Cube ι => fun i : {i // P i} => x i) (ProductMeasure.weight p) z =
      ProductMeasure.weight p z := by
  unfold mass
  rw [Fintype.sum_equiv (restrictionFiberEquiv P z)
    (fun x => ProductMeasure.weight p x.val)
    (fun y => ProductMeasure.weight p z * ProductMeasure.weight p y)
    (fun x => by
      change ProductMeasure.weight p x.val = ProductMeasure.weight p z *
        ProductMeasure.weight p (fun i : {i // ¬ P i} => x.val i)
      rw [ProductMeasure.weight_partition p P x.val, x.property])]
  rw [← Finset.mul_sum, ProductMeasure.sum_weight, mul_one]

/-- The coordinate conditional moment factors into the fixed assignment's mass
and the product average over the remaining coordinates. -/
theorem moment_restriction (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F : Cube ι → ℝ) (z : {i // P i} → Bool) :
    moment (fun x : Cube ι => fun i : {i // P i} => x i) (ProductMeasure.weight p) F z =
      ProductMeasure.weight p z * ProductMeasure.expectation p (fun y => F (merge P z y)) := by
  unfold moment ProductMeasure.expectation
  rw [Fintype.sum_equiv (restrictionFiberEquiv P z)
    (fun x => ProductMeasure.weight p x.val * F x.val)
    (fun y => ProductMeasure.weight p z * (ProductMeasure.weight p y * F (merge P z y)))
    (fun x => by
      have hx : merge P z (fun i : {i // ¬ P i} => x.val i) = x.val :=
        congrArg Subtype.val ((restrictionFiberEquiv P z).symm_apply_apply x)
      change ProductMeasure.weight p x.val * F x.val = ProductMeasure.weight p z *
        (ProductMeasure.weight p (fun i : {i // ¬ P i} => x.val i) *
          F (merge P z (fun i => x.val i)))
      rw [hx, ProductMeasure.weight_partition p P x.val, x.property]
      ring)]
  rw [← Finset.mul_sum]

/-- Conditioning a product law on some coordinates leaves its complementary
coordinates independent with their original bias. -/
theorem mean_restriction {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (P : ι → Prop) [DecidablePred P] (F : Cube ι → ℝ) (z : {i // P i} → Bool) :
    mean (fun x : Cube ι => fun i : {i // P i} => x i) (ProductMeasure.weight p) F z =
      ProductMeasure.expectation p (fun y => F (merge P z y)) := by
  unfold mean
  rw [mass_restriction, moment_restriction]
  have hn := (ProductMeasure.weight_pos hp0 hp1 z).ne'
  field_simp

/-- The numerical encoding of a Boolean function preserves order. -/
theorem value_monotone : Monotone value := by
  intro a b h
  cases a <;> cases b <;> simp_all [value, show ¬ ((true : Bool) ≤ false) by decide]

/-- Thresholding a real number at one half preserves order. -/
theorem threshold_monotone : Monotone threshold := by
  intro a b hab
  by_cases ha : (1/2:ℝ) < a
  · have hb : (1/2:ℝ) < b := ha.trans_le hab
    rw [show threshold a = true from decide_eq_true ha,
      show threshold b = true from decide_eq_true hb]
  · rw [show threshold a = false from decide_eq_false ha]
    exact Bool.false_le _

/-- A conditional mean of an increasing Boolean function on a fixed coordinate
set is increasing in the revealed assignment. -/
theorem mean_restriction_monotone {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (P : ι → Prop) [DecidablePred P] (f : Cube ι → Bool) (hf : Monotone f) :
    Monotone (mean (fun x : Cube ι => fun i : {i // P i} => x i)
      (ProductMeasure.weight p) (fun x => value (f x))) := by
  intro z z' hzz
  rw [mean_restriction hp0 hp1, mean_restriction hp0 hp1]
  apply ProductMeasure.expectation_mono hp0.le hp1.le
  intro y
  apply value_monotone
  apply hf
  intro i
  by_cases hi : P i
  · simpa [merge, hi] using hzz (⟨i,hi⟩ : {i // P i})
  · simp [merge, hi]

/-- The optimal Bayes decoder on a fixed coordinate set is increasing whenever
the target is increasing. -/
theorem coordinate_decoder_monotone {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (P : ι → Prop) [DecidablePred P] (f : Cube ι → Bool) (hf : Monotone f) :
    Monotone (decoder (fun x : Cube ι => fun i : {i // P i} => x i)
      (ProductMeasure.weight p) f) := by
  intro x y hxy
  apply threshold_monotone
  apply mean_restriction_monotone hp0 hp1 P f hf
  intro i
  exact hxy i

end CoordinatePartition
section Localization

omit [Fintype β] in
/-- Fiber masses written as ordinary finite sums with indicators. -/
theorem mass_eq_indicator_sum (φ : α → β) (w : α → ℝ) (b : β) :
    mass φ w b = ∑ a, if φ a = b then w a else 0 := by
  classical
  unfold mass
  simpa only [Finset.sum_filter] using
    (Finset.sum_subtype (Finset.univ.filter (fun a => φ a = b)) (by simp) w).symm

omit [Fintype β] in
/-- Fiber first moments written as ordinary finite sums with indicators. -/
theorem moment_eq_indicator_sum (φ : α → β) (w F : α → ℝ) (b : β) :
    moment φ w F b = ∑ a, if φ a = b then w a * F a else 0 := by
  classical
  unfold moment
  simpa only [Finset.sum_filter] using
    (Finset.sum_subtype (Finset.univ.filter (fun a => φ a = b)) (by simp)
      (fun a => w a * F a)).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype β] in
theorem mass_eq_expectation (p : ℝ) (φ : Cube ι → β) (b : β) :
    mass φ (ProductMeasure.weight p) b =
      ProductMeasure.expectation p (fun x => if φ x = b then 1 else 0) := by
  simp [mass_eq_indicator_sum, ProductMeasure.expectation, mul_ite]

omit [Fintype β] in
theorem moment_eq_expectation (p : ℝ) (φ : Cube ι → β) (F : Cube ι → ℝ) (b : β) :
    moment φ (ProductMeasure.weight p) F b =
      ProductMeasure.expectation p (fun x => if φ x = b then F x else 0) := by
  simp [moment_eq_indicator_sum, ProductMeasure.expectation, mul_ite]

omit [Fintype β] in
/-- A local partition has the same atom masses in the global and restricted cubes. -/
theorem mass_localization (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (φ : Cube ι → β) (hφ : ∀ x y, (∀ i, P i → x i = y i) → φ x = φ y) (b : β) :
    mass φ (ProductMeasure.weight p) b =
      mass (fun z => φ (ProductMeasure.extendFalse P z)) (ProductMeasure.weight p) b := by
  rw [mass_eq_expectation, mass_eq_expectation]
  apply ProductMeasure.expectation_local
  intro x y hxy
  rw [hφ x y hxy]

omit [Fintype β] in
/-- A local observable and local partition have the same conditional moment
when computed only on the coordinates they read. -/
theorem moment_localization (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (φ : Cube ι → β) (hφ : ∀ x y, (∀ i, P i → x i = y i) → φ x = φ y)
    (F : Cube ι → ℝ) (hF : ∀ x y, (∀ i, P i → x i = y i) → F x = F y) (b : β) :
    moment φ (ProductMeasure.weight p) F b =
      moment (fun z => φ (ProductMeasure.extendFalse P z)) (ProductMeasure.weight p)
        (fun z => F (ProductMeasure.extendFalse P z)) b := by
  rw [moment_eq_expectation, moment_eq_expectation]
  apply ProductMeasure.expectation_local
  intro x y hxy
  rw [hφ x y hxy, hF x y hxy]

omit [Fintype β] in
/-- Exact localization of conditional expectation for a local observable and
local partition. This is the restricted-atom interface used by Hatami's proof. -/
theorem conditional_localization (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (φ : Cube ι → β) (hφ : ∀ x y, (∀ i, P i → x i = y i) → φ x = φ y)
    (F : Cube ι → ℝ) (hF : ∀ x y, (∀ i, P i → x i = y i) → F x = F y)
    (x : Cube ι) :
    conditional φ (ProductMeasure.weight p) F x =
      conditional (fun z => φ (ProductMeasure.extendFalse P z)) (ProductMeasure.weight p)
        (fun z => F (ProductMeasure.extendFalse P z)) (fun i => x i) := by
  unfold conditional mean
  rw [moment_localization p P φ hφ F hF, mass_localization p P φ hφ]
  have hx : φ x = φ (ProductMeasure.extendFalse P (fun i => x i)) := by
    apply hφ
    intro i hi
    simp [ProductMeasure.extendFalse, hi]
  rw [hx]

end Localization
end NarrowDNF.ConditionalExpectation
