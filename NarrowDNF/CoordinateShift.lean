import NarrowDNF.Adaptive
import NarrowDNF.FiberShift

/-!
# Coordinate shifts on Boolean functions

The unbranched shift formulas are equivalent to the two-slice definitions in
equation (7) of arXiv:2609.00240v1, by Boolean idempotence. This file concerns
monotonicity; the global biased-error bound requires a separate finite-sum
argument.
-/

namespace NarrowDNF

variable {ι : Type*} [DecidableEq ι]

def lowerInput (i : ι) (x : Cube ι) : Cube ι := Function.update x i false

def upperInput (i : ι) (x : Cube ι) : Cube ι := Function.update x i true

def upperShift (i : ι) (v : Cube ι → Bool) (x : Cube ι) : Bool :=
  v x || v (lowerInput i x)

def lowerShift (i : ι) (v : Cube ι → Bool) (x : Cube ι) : Bool :=
  v x && v (upperInput i x)

@[simp] theorem upperShift_lowerInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    upperShift i v (lowerInput i x) = v (lowerInput i x) := by
  simp [upperShift, lowerInput]

@[simp] theorem upperShift_upperInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    upperShift i v (upperInput i x) = (v (lowerInput i x) || v (upperInput i x)) := by
  simp [upperShift, lowerInput, upperInput, Bool.or_comm]

@[simp] theorem lowerShift_lowerInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    lowerShift i v (lowerInput i x) = (v (lowerInput i x) && v (upperInput i x)) := by
  simp [lowerShift, lowerInput, upperInput]

@[simp] theorem lowerShift_upperInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    lowerShift i v (upperInput i x) = v (upperInput i x) := by
  simp [lowerShift, upperInput]

theorem lowerInput_le (i : ι) (x : Cube ι) : lowerInput i x ≤ x := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [lowerInput]
  · simp [lowerInput, hji]

theorem le_upperInput (i : ι) (x : Cube ι) : x ≤ upperInput i x := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [upperInput]
  · simp [upperInput, hji]

/-- Nondecreasing in one coordinate, with the other coordinates held fixed. -/
def CoordinateMonotone (i : ι) (v : Cube ι → Bool) : Prop :=
  ∀ x, v (lowerInput i x) ≤ v (upperInput i x)

theorem upperShift_coordinateMonotone (i : ι) (v : Cube ι → Bool) :
    CoordinateMonotone i (upperShift i v) := by
  intro x
  simpa [upperShift, lowerInput, upperInput, FiberShift.upper, Bool.or_comm] using
    FiberShift.upper_monotone (v (lowerInput i x), v (upperInput i x))

theorem lowerShift_coordinateMonotone (i : ι) (v : Cube ι → Bool) :
    CoordinateMonotone i (lowerShift i v) := by
  intro x
  simpa [lowerShift, lowerInput, upperInput, FiberShift.lower] using
    FiberShift.lower_monotone (v (lowerInput i x), v (upperInput i x))

theorem upperShift_preserves_coordinateMonotone {i j : ι} (hij : i ≠ j)
    {v : Cube ι → Bool} (hv : CoordinateMonotone j v) :
    CoordinateMonotone j (upperShift i v) := by
  intro x
  have h1 : v (lowerInput i (lowerInput j x)) ≤
      v (lowerInput i (upperInput j x)) := by
    simpa only [lowerInput, upperInput, Function.update_comm hij] using
      hv (lowerInput i x)
  exact (FiberShift.upper_preserves_order
    (v (lowerInput j x), v (lowerInput i (lowerInput j x)))
    (v (upperInput j x), v (lowerInput i (upperInput j x))) (hv x) h1).2

theorem lowerShift_preserves_coordinateMonotone {i j : ι} (hij : i ≠ j)
    {v : Cube ι → Bool} (hv : CoordinateMonotone j v) :
    CoordinateMonotone j (lowerShift i v) := by
  intro x
  have h1 : v (upperInput i (lowerInput j x)) ≤
      v (upperInput i (upperInput j x)) := by
    simpa only [lowerInput, upperInput, Function.update_comm hij] using
      hv (upperInput i x)
  exact (FiberShift.lower_preserves_order
    (v (lowerInput j x), v (upperInput i (lowerInput j x)))
    (v (upperInput j x), v (upperInput i (upperInput j x))) (hv x) h1).1

/-- A Boolean records whether the lower shift was chosen. -/
def shiftChoice (i : ι) (useLower : Bool) (v : Cube ι → Bool) : Cube ι → Bool :=
  if useLower then lowerShift i v else upperShift i v

/-- Apply shifts in list order; no commutativity of shifts is assumed. -/
def applyShifts : List (ι × Bool) → (Cube ι → Bool) → (Cube ι → Bool)
  | [], v => v
  | (i, b) :: rest, v => applyShifts rest (shiftChoice i b v)

theorem coordinateMonotone_le_upperInput {i : ι} {v : Cube ι → Bool}
    (hv : CoordinateMonotone i v) (x : Cube ι) : v x ≤ v (upperInput i x) := by
  cases hxi : x i
  · have hx : lowerInput i x = x := by
      simpa only [lowerInput, hxi] using Function.update_eq_self i x
    simpa only [hx] using hv x
  · have hx : upperInput i x = x := by
      simpa only [upperInput, hxi] using Function.update_eq_self i x
    simp only [hx, le_refl]

theorem coordinateMonotone_le_update {i : ι} {v : Cube ι → Bool}
    (hv : CoordinateMonotone i v) (x : Cube ι) (b : Bool) (hb : x i ≤ b) :
    v x ≤ v (Function.update x i b) := by
  cases b
  · have hxi : x i = false := Bool.eq_false_of_le_false hb
    have hx : Function.update x i false = x := by
      simpa only [hxi] using Function.update_eq_self i x
    simp only [hx, le_refl]
  · exact coordinateMonotone_le_upperInput hv x

/-- On a finite cube, coordinatewise monotonicity implies the usual
pointwise-order monotonicity. The proof changes the coordinates one at a time. -/
theorem monotone_of_coordinateMonotone [Fintype ι] {v : Cube ι → Bool}
    (hv : ∀ i, CoordinateMonotone i v) : Monotone v := by
  have hfinite : ∀ (S : Finset ι) (x y : Cube ι), x ≤ y →
      (∀ i, i ∉ S → x i = y i) → v x ≤ v y := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x y _ hagree
      have hxy : x = y := funext fun i => hagree i (by simp)
      simp only [hxy, le_refl]
    | @insert i S _ ih =>
      intro x y hxy hagree
      let z := Function.update x i (y i)
      have hxz : v x ≤ v z := coordinateMonotone_le_update (hv i) x (y i) (hxy i)
      apply hxz.trans
      apply ih z y
      · intro j
        by_cases hji : j = i
        · subst j
          simp [z]
        · simpa [z, hji] using hxy j
      · intro j hjS
        by_cases hji : j = i
        · subst j
          simp [z]
        · simpa [z, hji] using hagree j (by simp [hji, hjS])
  intro x y hxy
  exact hfinite Finset.univ x y hxy (by simp)

theorem coordinateMonotone_of_monotone {v : Cube ι → Bool} (hv : Monotone v)
    (i : ι) : CoordinateMonotone i v := by
  intro x
  exact hv ((lowerInput_le i x).trans (le_upperInput i x))

theorem shiftChoice_coordinateMonotone (i : ι) (b : Bool) (v : Cube ι → Bool) :
    CoordinateMonotone i (shiftChoice i b v) := by
  cases b
  · exact upperShift_coordinateMonotone i v
  · exact lowerShift_coordinateMonotone i v

/-- Each chosen shift preserves monotonicity in any already monotone
coordinate, including its own coordinate. -/
theorem shiftChoice_preserves_coordinateMonotone (i j : ι) (b : Bool)
    {v : Cube ι → Bool} (hv : CoordinateMonotone j v) :
    CoordinateMonotone j (shiftChoice i b v) := by
  by_cases hij : i = j
  · subst i
    exact shiftChoice_coordinateMonotone j b v
  · cases b
    · exact upperShift_preserves_coordinateMonotone hij hv
    · exact lowerShift_preserves_coordinateMonotone hij hv

theorem applyShifts_preserves_coordinateMonotone (shifts : List (ι × Bool))
    (j : ι) {v : Cube ι → Bool} (hv : CoordinateMonotone j v) :
    CoordinateMonotone j (applyShifts shifts v) := by
  induction shifts generalizing v with
  | nil => exact hv
  | cons a rest ih =>
    exact ih (shiftChoice_preserves_coordinateMonotone a.1 j a.2 hv)

/-- Once a coordinate has been processed, it is monotone in the final output. -/
theorem applyShifts_coordinateMonotone_of_mem (shifts : List (ι × Bool))
    (j : ι) (hj : j ∈ shifts.map Prod.fst) (v : Cube ι → Bool) :
    CoordinateMonotone j (applyShifts shifts v) := by
  induction shifts generalizing v with
  | nil => simp at hj
  | cons a rest ih =>
    rcases a with ⟨i, b⟩
    simp only [List.map_cons, List.mem_cons] at hj
    rcases hj with hji | hj
    · subst j
      exact applyShifts_preserves_coordinateMonotone rest i
        (shiftChoice_coordinateMonotone i b v)
    · exact ih hj (shiftChoice i b v)

/-- Processing every coordinate yields an increasing function, regardless
of processing order, shift choices, or repetitions of coordinates. -/
theorem applyShifts_monotone [Fintype ι] (shifts : List (ι × Bool))
    (hcovers : ∀ i, i ∈ shifts.map Prod.fst) (v : Cube ι → Bool) :
    Monotone (applyShifts shifts v) := by
  apply monotone_of_coordinateMonotone
  intro i
  exact applyShifts_coordinateMonotone_of_mem shifts i (hcovers i) v

end NarrowDNF
