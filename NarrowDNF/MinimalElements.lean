import NarrowDNF.Certificates

namespace NarrowDNF
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def support (x : Cube ι) : Finset ι := Finset.univ.filter fun i => x i = true

def termPoint (T : Finset ι) : Cube ι := fun i => decide (i ∈ T)

def MinimalAccepted (f : Cube ι → Prop) (x : Cube ι) : Prop :=
  f x ∧ ∀ y, y ≤ x → f y → y = x

@[simp] theorem support_termPoint (T : Finset ι) : support (termPoint T) = T := by
  ext i
  simp [support, termPoint]

omit [Fintype ι] in
theorem termPoint_holds (T : Finset ι) : TermHolds T (termPoint T) := by
  intro i hi
  simp [termPoint, hi]

omit [Fintype ι] in
theorem termPoint_le_of_holds {T : Finset ι} {x : Cube ι} (hx : TermHolds T x) :
    termPoint T ≤ x := by
  intro i
  by_cases hi : i ∈ T
  · simp [termPoint, hi, hx i hi]
  · simp [termPoint, hi]

omit [Fintype ι] in
/-- Every minimal accepted point of a positive DNF is the incidence vector of
one of its terms. This proves the width-to-minimal-element bridge used in
Conjecture 1.1 without changing its meaning. -/
theorem minimal_dnf_eq_term (terms : Finset (Finset ι)) {x : Cube ι}
    (hx : MinimalAccepted (DNFHolds terms) x) : ∃ T ∈ terms, termPoint T = x := by
  obtain ⟨T, hT, hTx⟩ := hx.1
  exact ⟨T, hT, hx.2 (termPoint T) (termPoint_le_of_holds hTx)
    ⟨T, hT, termPoint_holds T⟩⟩

theorem minimal_dnf_support_card_le (terms : Finset (Finset ι)) (w : ℕ)
    (hw : ∀ T ∈ terms, T.card ≤ w) {x : Cube ι}
    (hx : MinimalAccepted (DNFHolds terms) x) : (support x).card ≤ w := by
  obtain ⟨T, hT, rfl⟩ := minimal_dnf_eq_term terms hx
  simpa using hw T hT

end NarrowDNF
