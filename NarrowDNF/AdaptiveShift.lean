import NarrowDNF.CoordinateShift
import Mathlib.Data.Finset.Insert

/-!
# Adaptive atoms under shifts

The precise content of Lemma 3.2 and Appendix B of arXiv:2609.00240v1.
All activations carry the locality field from `Activation`; no decoder or atom
recovery oracle is assumed. The unbranched formulas for shifts are equivalent
to the paper's two-slice formulas by Boolean idempotence.
-/

namespace NarrowDNF

variable {ι : Type*} [DecidableEq ι]

def forceInput (D : Finset ι) (x : Cube ι) : Cube ι :=
  fun i => if i ∈ D then true else x i

theorem le_forceInput (D : Finset ι) (x : Cube ι) : x ≤ forceInput D x := by
  intro i
  simp only [forceInput]
  split <;> simp_all

theorem forceInput_mono (D : Finset ι) : Monotone (forceInput D) := by
  intro x y hxy i
  simp only [forceInput]
  split
  · exact le_rfl
  · exact hxy i

theorem forceInput_singleton (i : ι) (x : Cube ι) :
    forceInput {i} x = upperInput i x := by
  funext j
  simp [forceInput, upperInput, Function.update_apply]

namespace Activation

omit [DecidableEq ι] in
/-- Locality reconstructs a complete atom from labels on any common superset
of both active unions. This is the elementary recovery fact used below. -/
theorem sameAtom_of_active_subset_of_agree {J : Activation ι} {x y : Cube ι}
    {B : Set ι} (hx : J.active x ⊆ B) (hy : J.active y ⊆ B)
    (hxy : ∀ i ∈ B, x i = y i) : J.SameAtom x y := by
  have forward : ∀ S, J.fires S x → J.fires S y := by
    intro S hS
    apply (J.locality S x y ?_).mp hS
    intro i hi
    exact hxy i (hx (mem_active_of_fires hS hi))
  have backward : ∀ S, J.fires S y → J.fires S x := by
    intro S hS
    apply (J.locality S y x ?_).mp hS
    intro i hi
    exact (hxy i (hy (mem_active_of_fires hS hi))).symm
  constructor
  · ext i
    constructor
    · rintro ⟨S, hi, hS⟩
      exact ⟨S, hi, forward S hS⟩
    · rintro ⟨S, hi, hS⟩
      exact ⟨S, hi, backward S hS⟩
  · intro i hi
    exact hxy i (hx hi)

/-- Lowering a fixed coordinate is a well-defined map on adaptive atoms. This
includes the case where the atom does not record that coordinate. -/
theorem sameAtom_lowerInput {J : Activation ι} (hJ : J.Increasing)
    {x y : Cube ι} (hxy : J.SameAtom x y) (i : ι) :
    J.SameAtom (lowerInput i x) (lowerInput i y) := by
  apply sameAtom_of_active_subset_of_agree
    (B := J.active x) (active_mono hJ (lowerInput_le i x))
  · rw [hxy.1]
    exact active_mono hJ (lowerInput_le i y)
  · intro j hj
    by_cases hji : j = i
    · subst j
      simp [lowerInput]
    · simpa [lowerInput, Function.update_apply, hji] using hxy.2 j hj

/-- An upper shift needs no refinement of the adaptive partition. -/
theorem measurable_upperShift {J : Activation ι} (hJ : J.Increasing)
    {v : Cube ι → Bool} (hv : J.Measurable v) (i : ι) :
    J.Measurable (upperShift i v) := by
  intro x y hxy
  unfold upperShift
  rw [hv x y hxy, hv _ _ (sameAtom_lowerInput hJ hxy i)]

/-- Forcing changes the activation test, but never the labels stored by its
adaptive atom. -/
def force (J : Activation ι) (D : Finset ι) : Activation ι where
  fires S x := J.fires S (forceInput D x)
  locality S x y hxy := J.locality S (forceInput D x) (forceInput D y) (by
    intro i hi
    simp only [forceInput]
    split
    · rfl
    · exact hxy i hi)

theorem force_active (J : Activation ι) (D : Finset ι) (x : Cube ι) :
    (J.force D).active x = J.active (forceInput D x) := rfl

theorem force_increasing {J : Activation ι} (hJ : J.Increasing) (D : Finset ι) :
    (J.force D).Increasing := by
  intro S x y hxy
  exact hJ S (forceInput_mono D hxy)

/-- A forced atom determines the original atom at the unforced input. -/
theorem force_refines {J : Activation ι} (hJ : J.Increasing) (D : Finset ι)
    {x y : Cube ι} (hxy : (J.force D).SameAtom x y) : J.SameAtom x y := by
  apply sameAtom_of_active_subset_of_agree
    (B := J.active (forceInput D x)) (active_mono hJ (le_forceInput D x))
  · rw [← force_active, hxy.1, force_active]
    exact active_mono hJ (le_forceInput D y)
  · exact hxy.2

/-- A forced atom also determines the original atom at the forced input.
The proof explicitly changes its recorded actual labels to forced labels. -/
theorem sameAtom_forceInput {J : Activation ι} (D : Finset ι)
    {x y : Cube ι} (hxy : (J.force D).SameAtom x y) :
    J.SameAtom (forceInput D x) (forceInput D y) := by
  constructor
  · exact hxy.1
  · intro i hi
    simp only [forceInput]
    split
    · rfl
    · exact hxy.2 i hi

/-- A lower shift is measurable for the one-coordinate forced refinement. -/
theorem measurable_lowerShift {J : Activation ι} (hJ : J.Increasing)
    {v : Cube ι → Bool} (hv : J.Measurable v) (i : ι) :
    (J.force {i}).Measurable (lowerShift i v) := by
  intro x y hxy
  have horiginal : v x = v y := hv x y (force_refines hJ {i} hxy)
  have hupper : J.SameAtom (upperInput i x) (upperInput i y) := by
    simpa only [forceInput_singleton] using sameAtom_forceInput {i} hxy
  unfold lowerShift
  rw [horiginal, hv _ _ hupper]

theorem forceInput_union (D E : Finset ι) (x : Cube ι) :
    forceInput D (forceInput E x) = forceInput (D ∪ E) x := by
  funext i
  by_cases hiD : i ∈ D <;> by_cases hiE : i ∈ E <;>
    simp [forceInput, hiD, hiE]

theorem force_force (J : Activation ι) (D E : Finset ι) :
    (J.force D).force E = J.force (D ∪ E) := by
  cases J with
  | mk fires hlocal =>
    simp only [force, forceInput_union]

theorem force_empty (J : Activation ι) : J.force ∅ = J := by
  have hinput : ∀ x : Cube ι, forceInput ∅ x = x := by
    intro x
    funext i
    simp [forceInput]
  cases J with
  | mk fires hlocal =>
    simp only [force, hinput]

/-- Coordinates on which at least one lower shift occurs. Repeated coordinates
are intentionally allowed, and the chosen processing order is retained in the
separate list passed to `applyShifts`. -/
def lowerCoordinates : List (ι × Bool) → Finset ι
  | [] => ∅
  | (i, b) :: rest => if b then insert i (lowerCoordinates rest) else lowerCoordinates rest

/-- The complete finite-sequence closure statement of Lemma 3.2. It permits
arbitrary interleavings and repetitions, with no commutativity assumption. -/
theorem measurable_applyShifts (steps : List (ι × Bool)) {J : Activation ι}
    (hJ : J.Increasing) {v : Cube ι → Bool} (hv : J.Measurable v) :
    (J.force (lowerCoordinates steps)).Measurable (applyShifts steps v) := by
  induction steps generalizing J v with
  | nil => simpa only [lowerCoordinates, force_empty, applyShifts] using hv
  | cons step rest ih =>
    rcases step with ⟨i, b⟩
    cases b
    · simpa only [lowerCoordinates, Bool.false_eq_true, if_false, applyShifts,
        shiftChoice] using ih hJ (measurable_upperShift hJ hv i)
    · simpa only [lowerCoordinates, if_true, applyShifts, shiftChoice, force_force,
        Finset.singleton_union] using
        ih (force_increasing hJ {i}) (measurable_lowerShift hJ hv i)

end Activation
end NarrowDNF
