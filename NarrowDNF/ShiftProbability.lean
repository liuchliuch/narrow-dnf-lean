import NarrowDNF.CoordinateShift
import NarrowDNF.ProductMeasure

/-!
# Randomized coordinate shifting under the biased product measure

This file proves the full error inequality of Lemma 3.1 and the iterated
expectation inequality (8) in arXiv:2609.00240v1. Random choices form an
explicit Bernoulli product cube; the independence needed by iteration is
derived from the finite-sum Fubini formula.
-/

noncomputable section

namespace NarrowDNF.ShiftProbability

open ProductMeasure

variable {ι : Type*} [DecidableEq ι]

theorem update_insertBit (i : ι) (a b : Bool) (z : {j // j ≠ i} → Bool) :
    Function.update (insertBit i a z) i b = insertBit i b z := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simpa only [Function.update_of_ne hji] using
      (insertBit_away i a z ⟨j, hji⟩).trans (insertBit_away i b z ⟨j, hji⟩).symm

@[simp] theorem lowerInput_insertBit (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    lowerInput i (insertBit i b z) = insertBit i false z :=
  update_insertBit i b false z

@[simp] theorem upperInput_insertBit (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    upperInput i (insertBit i b z) = insertBit i true z :=
  update_insertBit i b true z

variable [Fintype ι]

/-- Global disagreement is the expectation of the conditional fiber error. -/
theorem error_eq_fiber_expectation (p : ℝ) (i : ι) (f v : Cube ι → Bool) :
    ProductMeasure.error p f v = expectation p (fun z =>
      FiberShift.error p (f (insertBit i false z), f (insertBit i true z))
        (v (insertBit i false z), v (insertBit i true z))) := by
  unfold ProductMeasure.error probability
  rw [expectation_split p i, ← expectation_const_mul, ← expectation_const_mul,
    ← expectation_add]
  congr 1
  funext z
  by_cases h0 : f (insertBit i false z) = v (insertBit i false z) <;>
    by_cases h1 : f (insertBit i true z) = v (insertBit i true z) <;>
      simp [FiberShift.error, FiberShift.mismatch, h0, h1]

/-- Full error bound in Lemma 3.1: the random shift choice is independent
of the input, and uses upper with mass `1-p` and lower with mass `p`. -/
theorem one_coordinate_error_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : ι) (f v : Cube ι → Bool) (hf : Monotone f) :
    (1-p) * ProductMeasure.error p f (upperShift i v) +
        p * ProductMeasure.error p f (lowerShift i v) ≤ ProductMeasure.error p f v := by
  rw [error_eq_fiber_expectation p i f (upperShift i v),
    error_eq_fiber_expectation p i f (lowerShift i v), error_eq_fiber_expectation p i f v,
    ← expectation_const_mul, ← expectation_const_mul, ← expectation_add]
  apply expectation_mono hp0 hp1
  intro z
  have hmono : f (insertBit i false z) ≤ f (insertBit i true z) := by
    simpa only [lowerInput_insertBit, upperInput_insertBit] using
      coordinateMonotone_of_monotone hf i (insertBit i false z)
  simpa [upperShift, lowerShift, FiberShift.upper, FiberShift.lower, Bool.or_comm] using
    FiberShift.randomized_error_le p hp0 hp1
      (f (insertBit i false z), f (insertBit i true z))
      (v (insertBit i false z), v (insertBit i true z)) hmono

/-- An observable unchanged by coordinate updates has the same expectation
after fixing that coordinate to either value. This is proved from Fubini. -/
theorem expectation_of_ignores_coordinate (p : ℝ) (i : ι) (b : Bool)
    (F : Cube ι → ℝ) (hF : ∀ x c, F (Function.update x i c) = F x) :
    expectation p F = expectation p (fun z => F (insertBit i b z)) := by
  have heq (c : Bool) : (fun z => F (insertBit i c z)) =
      (fun z => F (insertBit i b z)) := by
    funext z
    simpa only [update_insertBit] using (hF (insertBit i c z) b).symm
  rw [expectation_split p i, heq false, heq true]
  ring

/-- Exact independence of a selected Bernoulli bit from an observable of
the remaining coordinates. There is no independence assumption in this lemma. -/
theorem expectation_coordinate_bind (p : ℝ) (i : ι) (F : Bool → Cube ι → ℝ)
    (hF : ∀ b x c, F b (Function.update x i c) = F b x) :
    expectation p (fun d => F (d i) d) =
      (1-p) * expectation p (F false) + p * expectation p (F true) := by
  rw [expectation_split p i]
  simp only [insertBit_at]
  rw [expectation_of_ignores_coordinate p i false (F false) (hF false),
    expectation_of_ignores_coordinate p i true (F true) (hF true)]

/-- Apply a fixed coordinate order, using the corresponding bits of `d`
as the lower/upper choices. -/
def shiftByChoices (order : List ι) (d : Cube ι) (v : Cube ι → Bool) : Cube ι → Bool :=
  applyShifts (order.map fun i => (i, d i)) v

omit [Fintype ι] in
@[simp] theorem shiftByChoices_nil (d : Cube ι) (v : Cube ι → Bool) :
    shiftByChoices [] d v = v := rfl

omit [Fintype ι] in
@[simp] theorem shiftByChoices_cons (i : ι) (order : List ι)
    (d : Cube ι) (v : Cube ι → Bool) :
    shiftByChoices (i :: order) d v =
      shiftByChoices order d (shiftChoice i (d i) v) := rfl

omit [Fintype ι] in
theorem shiftByChoices_congr (order : List ι) (d e : Cube ι)
    (hde : ∀ i ∈ order, d i = e i) (v : Cube ι → Bool) :
    shiftByChoices order d v = shiftByChoices order e v := by
  induction order generalizing v with
  | nil => rfl
  | cons i rest ih =>
    rw [shiftByChoices_cons, shiftByChoices_cons, hde i (by simp)]
    exact ih (fun j hj => hde j (by simp [hj])) (shiftChoice i (e i) v)

omit [Fintype ι] in
theorem shiftByChoices_update_of_not_mem (order : List ι) (i : ι) (hi : i ∉ order)
    (d : Cube ι) (b : Bool) (v : Cube ι → Bool) :
    shiftByChoices order (Function.update d i b) v = shiftByChoices order d v := by
  apply shiftByChoices_congr
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  simp [hji]

/-- Fubini recursion for the exact expected error. Nonrepetition makes the
remaining shifts independent of the bit controlling the first shift. -/
theorem expected_error_cons (p : ℝ) (i : ι) (order : List ι) (hi : i ∉ order)
    (f v : Cube ι → Bool) :
    expectation p (fun d => ProductMeasure.error p f (shiftByChoices (i :: order) d v)) =
      (1-p) * expectation p (fun d => ProductMeasure.error p f
        (shiftByChoices order d (upperShift i v))) +
      p * expectation p (fun d => ProductMeasure.error p f
        (shiftByChoices order d (lowerShift i v))) := by
  simpa only [shiftByChoices_cons, shiftChoice, Bool.false_eq_true, if_false, if_true] using
    expectation_coordinate_bind p i
      (fun b d => ProductMeasure.error p f (shiftByChoices order d (shiftChoice i b v)))
      (fun b d c => congrArg (ProductMeasure.error p f)
        (shiftByChoices_update_of_not_mem order i hi d c (shiftChoice i b v)))

/-- Equation (8)'s error inequality, strengthened to any nonrepeating partial
coordinate order. The random choice cube has the explicit product law `μ_p`. -/
theorem iterated_error_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (order : List ι) (hnodup : order.Nodup) (f v : Cube ι → Bool) (hf : Monotone f) :
    expectation p (fun d => ProductMeasure.error p f (shiftByChoices order d v)) ≤
      ProductMeasure.error p f v := by
  induction order generalizing v with
  | nil => simp
  | cons i rest ih =>
    obtain ⟨hi, hrest⟩ := List.nodup_cons.mp hnodup
    rw [expected_error_cons p i rest hi]
    apply le_trans _ (one_coordinate_error_le p hp0 hp1 i f v hf)
    exact add_le_add
      (mul_le_mul_of_nonneg_left (ih hrest (upperShift i v)) (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left (ih hrest (lowerShift i v)) hp0)

/-- The iterated bound stated directly in the shared `applyShifts` API. -/
theorem applyShifts_expected_error_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (order : List ι) (hnodup : order.Nodup) (f v : Cube ι → Bool) (hf : Monotone f) :
    expectation p (fun d => ProductMeasure.error p f
      (applyShifts (order.map fun i => (i, d i)) v)) ≤ ProductMeasure.error p f v :=
  iterated_error_le p hp0 hp1 order hnodup f v hf

theorem shiftByChoices_monotone (order : List ι) (hcovers : ∀ i, i ∈ order)
    (d : Cube ι) (v : Cube ι → Bool) : Monotone (shiftByChoices order d v) := by
  apply applyShifts_monotone
  intro i
  rw [List.map_map]
  change i ∈ List.map id order
  simpa only [List.map_id] using hcovers i

/-- The complete deterministic-monotonicity and random-error conclusion
obtained by processing every coordinate exactly once. -/
theorem iterated_shift_conclusion (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (order : List ι) (hnodup : order.Nodup) (hcovers : ∀ i, i ∈ order)
    (f v : Cube ι → Bool) (hf : Monotone f) :
    (∀ d, Monotone (shiftByChoices order d v)) ∧
      expectation p (fun d => ProductMeasure.error p f (shiftByChoices order d v)) ≤
        ProductMeasure.error p f v :=
  ⟨fun d => shiftByChoices_monotone order hcovers d v,
    iterated_error_le p hp0 hp1 order hnodup f v hf⟩

end NarrowDNF.ShiftProbability
