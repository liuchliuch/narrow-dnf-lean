import NarrowDNF.Adaptive
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace NarrowDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive conjunction, including the true empty conjunction. -/
def TermHolds (T : Finset ι) (x : Cube ι) : Prop := ∀ i ∈ T, x i = true

/-- A finite monotone DNF, including the false empty disjunction. -/
def DNFHolds (terms : Finset (Finset ι)) (x : Cube ι) : Prop :=
  ∃ T ∈ terms, TermHolds T x

omit [Fintype ι] [DecidableEq ι] in
theorem termHolds_mono (T : Finset ι) : Monotone (TermHolds T) := by
  intro x y hxy hx i hi
  have := hxy i
  cases hyi : y i
  · rw [hx i hi, hyi] at this
    exact False.elim ((by decide : ¬(true ≤ false)) this)
  · rfl

omit [Fintype ι] [DecidableEq ι] in
theorem dnfHolds_mono (terms : Finset (Finset ι)) : Monotone (DNFHolds terms) := by
  intro x y hxy hx
  obtain ⟨T, hT, hxT⟩ := hx
  exact ⟨T, hT, termHolds_mono T hxy hxT⟩

namespace Activation

noncomputable def activeFinset (J : Activation ι) (x : Cube ι) : Finset ι :=
  by classical exact Finset.univ.filter fun i => i ∈ J.active x

noncomputable def certificate (J : Activation ι) (x : Cube ι) : Finset ι :=
  by classical exact (J.activeFinset x).filter fun i => x i = true

omit [DecidableEq ι] in
@[simp] theorem mem_activeFinset (J : Activation ι) (x : Cube ι) (i : ι) :
    i ∈ J.activeFinset x ↔ i ∈ J.active x := by
  classical
  simp [activeFinset]

omit [DecidableEq ι] in
@[simp] theorem mem_certificate (J : Activation ι) (x : Cube ι) (i : ι) :
    i ∈ J.certificate x ↔ i ∈ J.active x ∧ x i = true := by
  classical
  simp [certificate]

omit [DecidableEq ι] in
theorem certificate_card_le (J : Activation ι) (x : Cube ι) :
    (J.certificate x).card ≤ (J.activeFinset x).card := Finset.card_filter_le _ _

omit [DecidableEq ι] in
theorem certificate_holds (J : Activation ι) (x : Cube ι) :
    TermHolds (J.certificate x) x := by
  intro i hi
  exact ((mem_certificate J x i).mp hi).2

omit [DecidableEq ι] in
theorem certificate_forces {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u)
    {x : Cube ι} (hx : u x = true) {y : Cube ι}
    (hy : TermHolds (J.certificate x) y) : u y = true := by
  apply positive_certificate hJ hu hm hx
  intro i hi hxi
  exact hy i ((mem_certificate J x i).mpr ⟨hi, hxi⟩)

/-- Keep exactly the certificates of accepted inputs whose certificate has
cardinality at most the cutoff. This explicitly constructs a finite DNF. -/
noncomputable def truncatedTerms (J : Activation ι) (u : Cube ι → Bool)
    (w : ℕ) : Finset (Finset ι) :=
  by
    classical
    exact (Finset.univ.filter fun x => u x = true ∧ (J.certificate x).card ≤ w).image J.certificate

theorem truncatedTerms_width (J : Activation ι) (u : Cube ι → Bool) (w : ℕ)
    {T : Finset ι} (hT : T ∈ J.truncatedTerms u w) : T.card ≤ w := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
  exact (Finset.mem_filter.mp hx).2.2

theorem truncatedTerms_sound {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ)
    {y : Cube ι} (hy : DNFHolds (J.truncatedTerms u w) y) : u y = true := by
  classical
  obtain ⟨T, hT, hyT⟩ := hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
  exact certificate_forces hJ hu hm (Finset.mem_filter.mp hx).2.1 hyT

theorem truncatedTerms_complete {J : Activation ι} {u : Cube ι → Bool}
    {w : ℕ} {x : Cube ι} (hx : u x = true)
    (hw : (J.certificate x).card ≤ w) : DNFHolds (J.truncatedTerms u w) x := by
  classical
  refine ⟨J.certificate x, Finset.mem_image.mpr ⟨x, ?_, rfl⟩, certificate_holds J x⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, hw⟩

/-- Deterministic part of the truncation estimate: all lost accepted points
have certificate size larger than the cutoff. -/
theorem truncatedTerms_missed_large {J : Activation ι} {u : Cube ι → Bool}
    {w : ℕ} {x : Cube ι} (hx : u x = true)
    (hmiss : ¬ DNFHolds (J.truncatedTerms u w) x) : w < (J.certificate x).card := by
  exact Nat.lt_of_not_ge fun hw => hmiss (truncatedTerms_complete hx hw)

end Activation
end NarrowDNF
