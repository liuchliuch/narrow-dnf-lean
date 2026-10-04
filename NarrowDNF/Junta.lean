import NarrowDNF.MainStatements
import NarrowDNF.PaperCertificates

noncomputable section
namespace NarrowDNF
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Dependence only on a specified set of coordinates. -/
def IsJuntaOn (J : Finset ι) (f : Cube ι → Bool) : Prop :=
  ∀ x y, (∀ i ∈ J, x i = y i) → f x = f y

/-- One always-active local block models a fixed-coordinate junta. -/
def juntaActivation (J : Finset ι) : Activation ι where
  fires S _ := S = J
  locality _ _ _ _ := Iff.rfl

omit [Fintype ι] [DecidableEq ι] in
theorem juntaActivation_increasing (J : Finset ι) : (juntaActivation J).Increasing := by
  intro S x y _ h
  exact h

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem juntaActivation_active (J : Finset ι) (x : Cube ι) :
    (juntaActivation J).active x = (J : Set ι) := by
  ext i
  simp only [Activation.active, juntaActivation, Set.mem_setOf_eq, Finset.mem_coe]
  constructor
  · rintro ⟨S, hi, rfl⟩
    exact hi
  · intro hi
    exact ⟨J, hi, rfl⟩

omit [DecidableEq ι] in
@[simp] theorem juntaActivation_activeFinset (J : Finset ι) (x : Cube ι) :
    (juntaActivation J).activeFinset x = J := by
  ext i
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem junta_measurable (J : Finset ι) {f : Cube ι → Bool} (hf : IsJuntaOn J f) :
    (juntaActivation J).Measurable f := by
  intro x y hxy
  apply hf x y
  intro i hi
  exact hxy.2 i (by simpa using hi)

/-- Every increasing J-junta is exactly a positive DNF of width at most |J|.
This supplies the representation step in the all-bias reduction. -/
theorem monotone_junta_eq_dnf (J : Finset ι) {f : Cube ι → Bool}
    (hf : Monotone f) (hJ : IsJuntaOn J f) :
    ∃ terms : Finset (Finset ι), (∀ T ∈ terms, T.card ≤ J.card) ∧ evalDNF terms = f := by
  let A := juntaActivation J
  let terms := A.truncatedTerms f J.card
  have hA : A.Increasing := juntaActivation_increasing J
  have hm : A.Measurable f := junta_measurable J hJ
  refine ⟨terms, fun T hT => Activation.truncatedTerms_width A f J.card hT, ?_⟩
  funext x
  change A.truncatedDNF f J.card x = f x
  apply le_antisymm
  · exact Activation.truncatedDNF_le hA hf hm J.card x
  · cases hfx : f x
    · exact Bool.false_le _
    · have hcard : (A.certificate x).card ≤ J.card := by
        simpa [A] using Activation.certificate_card_le A x
      have hx := Activation.truncatedTerms_complete hfx hcard
      rw [(Activation.truncatedDNF_eq_true A f J.card x).mpr hx]

end NarrowDNF
