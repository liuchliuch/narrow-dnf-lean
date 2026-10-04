import NarrowDNF.MainStatements
import Mathlib.Data.Finset.Max

/-!
# Canonical monotone DNF from minimal accepted points

The terms are exactly the supports of minimal accepted points. This closes the
converse of `minimal_dnf_support_card_le`: for an increasing family, bounded
minimal Hamming weight is equivalent to exact representability by a positive
DNF of bounded width. Empty disjunctions and empty conjunctions are retained.
-/

namespace NarrowDNF.CanonicalDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem termPoint_support (x : Cube ι) : termPoint (support x) = x := by
  funext i
  cases h : x i <;> simp [termPoint, support, h]

theorem support_injective : Function.Injective (support : Cube ι → Finset ι) := by
  intro x y h
  simpa using congrArg termPoint h

omit [DecidableEq ι] in
theorem support_mono : Monotone (support : Cube ι → Finset ι) := by
  intro x y hxy i hi
  have hxi : x i = true := (Finset.mem_filter.mp hi).2
  have hyi : y i = true := by
    have h := hxy i
    cases h' : y i <;> simp_all
  simp [support, hyi]

@[simp] theorem termHolds_support_iff (x y : Cube ι) :
    TermHolds (support x) y ↔ x ≤ y := by
  constructor
  · intro h
    simpa using termPoint_le_of_holds h
  · intro h i hi
    have hxi : x i = true := (Finset.mem_filter.mp hi).2
    have hi' := h i
    cases hyi : y i <;> simp_all

/-- Every accepted point lies above a minimal accepted point. No monotonicity
is needed for this finite-poset fact. -/
theorem exists_minimalAccepted_le {f : Cube ι → Prop} {x : Cube ι} (hx : f x) :
    ∃ y, y ≤ x ∧ MinimalAccepted f y := by
  classical
  let A : Finset (Cube ι) := Finset.univ.filter fun y => y ≤ x ∧ f y
  have hA : A.Nonempty := ⟨x, by simp [A, hx]⟩
  obtain ⟨y, hy, hmin⟩ := A.exists_min_image (fun y => (support y).card) hA
  have hy' : y ≤ x ∧ f y := (Finset.mem_filter.mp hy).2
  refine ⟨y, hy'.1, hy'.2, ?_⟩
  intro z hzy hz
  apply support_injective
  apply Finset.eq_of_subset_of_card_le (support_mono hzy)
  exact hmin z (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hzy.trans hy'.1, hz⟩)

/-- The canonical positive DNF has one term for each minimal accepted point. -/
noncomputable def terms (f : Cube ι → Prop) : Finset (Finset ι) := by
  classical
  exact (Finset.univ.filter (MinimalAccepted f)).image support

@[simp] theorem mem_terms {f : Cube ι → Prop} {T : Finset ι} :
    T ∈ terms f ↔ MinimalAccepted f (termPoint T) := by
  classical
  constructor
  · intro hT
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
    simpa using (Finset.mem_filter.mp hx).2
  · intro hT
    exact Finset.mem_image.mpr ⟨termPoint T,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩, support_termPoint T⟩

/-- Exact representation, not only approximation or one-sided inclusion. -/
theorem holds_iff {f : Cube ι → Prop} (hf : Monotone f) (x : Cube ι) :
    DNFHolds (terms f) x ↔ f x := by
  constructor
  · rintro ⟨T, hT, hx⟩
    exact hf (termPoint_le_of_holds hx) (mem_terms.mp hT).1
  · intro hx
    obtain ⟨y, hyx, hy⟩ := exists_minimalAccepted_le hx
    refine ⟨support y, ?_, (termHolds_support_iff y x).mpr hyx⟩
    exact mem_terms.mpr (by simpa using hy)

theorem width_le {f : Cube ι → Prop} {w : ℕ}
    (hw : ∀ x, MinimalAccepted f x → (support x).card ≤ w) :
    ∀ T ∈ terms f, T.card ≤ w := by
  intro T hT
  simpa using hw (termPoint T) (mem_terms.mp hT)

/-- Increasing families have width at most `w` exactly when all their minimal
accepted points have Hamming weight at most `w`. -/
theorem bounded_minimal_iff_exists_dnf {f : Cube ι → Prop} (hf : Monotone f) (w : ℕ) :
    (∀ x, MinimalAccepted f x → (support x).card ≤ w) ↔
      ∃ A : Finset (Finset ι), (∀ T ∈ A, T.card ≤ w) ∧
        ∀ x, DNFHolds A x ↔ f x := by
  constructor
  · intro hw
    exact ⟨terms f, width_le hw, holds_iff hf⟩
  · rintro ⟨A, hA, hAf⟩ x hx
    have hfx : MinimalAccepted (DNFHolds A) x := by
      refine ⟨(hAf x).mpr hx.1, ?_⟩
      intro y hy hyA
      exact hx.2 y hy ((hAf y).mp hyA)
    exact minimal_dnf_support_card_le A w hA hfx

/-- The Boolean-function formulation uses the same canonical terms. -/
theorem eval_eq {f : Cube ι → Bool} (hf : Monotone f) :
    evalDNF (terms fun x => f x = true) = f := by
  have hfp : Monotone (fun x => f x = true) := by
    intro x y hxy hx
    have h := hf hxy
    cases hy : f y <;> simp_all
  funext x
  apply Bool.eq_iff_iff.mpr
  simpa [evalDNF] using holds_iff hfp x

/-- The increasing-family formulation, as equality of sets of cube points. -/
theorem family_eq (A : Set (Cube ι)) (hA : Monotone (fun x => x ∈ A)) :
    {x | DNFHolds (terms (fun y => y ∈ A)) x} = A := by
  ext x
  exact holds_iff hA x

/-- Bounded minimal support gives an exact bounded-width Boolean DNF. -/
theorem bool_exists_dnf {f : Cube ι → Bool} (hf : Monotone f) {w : ℕ}
    (hw : ∀ x, MinimalAccepted (fun y => f y = true) x → (support x).card ≤ w) :
    ∃ A : Finset (Finset ι), (∀ T ∈ A, T.card ≤ w) ∧ evalDNF A = f :=
  ⟨terms (fun x => f x = true), width_le hw, eval_eq hf⟩

/-- The bounded-width equivalence also holds as exact Boolean-function equality. -/
theorem bool_bounded_minimal_iff_exists_dnf {f : Cube ι → Bool}
    (hf : Monotone f) (w : ℕ) :
    (∀ x, MinimalAccepted (fun y => f y = true) x → (support x).card ≤ w) ↔
      ∃ A : Finset (Finset ι), (∀ T ∈ A, T.card ≤ w) ∧ evalDNF A = f := by
  constructor
  · exact bool_exists_dnf hf
  · rintro ⟨A, hA, hAf⟩ x hx
    have hfx : MinimalAccepted (DNFHolds A) x := by
      have hholds (y : Cube ι) : DNFHolds A y ↔ f y = true := by
        rw [← hAf]
        simp [evalDNF]
      exact ⟨(hholds x).mpr hx.1, fun y hy hyA => hx.2 y hy ((hholds y).mp hyA)⟩
    exact minimal_dnf_support_card_le A w hA hfx

@[simp] theorem terms_false : terms (fun _ : Cube ι => False) = ∅ := by
  classical
  ext T
  simp [MinimalAccepted]

@[simp] theorem terms_true : terms (fun _ : Cube ι => True) = {∅} := by
  classical
  ext T
  simp only [mem_terms, Finset.mem_singleton]
  constructor
  · intro hT
    have h := hT.2 (termPoint ∅) (termPoint_le_of_holds (by simp [TermHolds])) trivial
    have hs := congrArg support h
    simpa using hs.symm
  · rintro rfl
    refine ⟨trivial, ?_⟩
    intro y hy _
    apply le_antisymm hy
    exact termPoint_le_of_holds (by simp [TermHolds])

/-- The empty family is represented by the empty disjunction, of width zero. -/
theorem false_width_zero :
    (∀ T ∈ terms (fun _ : Cube ι => False), T.card ≤ 0) ∧
      ∀ x, ¬ DNFHolds (terms (fun _ : Cube ι => False)) x := by
  simp [DNFHolds]

/-- The full family is represented by the true empty conjunction, of width zero. -/
theorem true_width_zero :
    (∀ T ∈ terms (fun _ : Cube ι => True), T.card ≤ 0) ∧
      ∀ x, DNFHolds (terms (fun _ : Cube ι => True)) x := by
  simp [DNFHolds, TermHolds]

end NarrowDNF.CanonicalDNF
