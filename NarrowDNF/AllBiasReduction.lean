import NarrowDNF.MainStatements
import NarrowDNF.ConstantApproximation
import NarrowDNF.Junta
import Mathlib.Tactic.Linarith

/-!
# The all-bias reduction in the proof of Conjecture 1.1

This module proves an explicit implication from the low-bias headline theorem
and the uniform compact-bias junta theorem. Naming these input propositions
does not assert them. The unconditional all-bias claim must separately supply
actual proofs of both inputs.
-/

noncomputable section
namespace NarrowDNF
open ProductMeasure Influence
attribute [local instance] Classical.propDecidable

/-- A dimension- and bias-uniform compact-interval junta theorem. The M is
chosen before n and p, and the approximating junta is increasing. This is a
proposition definition, not an axiom or an imported assertion. -/
def CompactBiasMonotoneJunta : Prop :=
  ∀ lam K ε : ℝ, 0 < lam → lam ≤ 1/2 → 0 < K → 0 < ε → ε < 1 →
    ∃ M : ℕ, ∀ (n : ℕ) (p : ℝ), lam ≤ p → p ≤ 1-lam →
      ∀ f : Cube (Fin n) → Bool, Monotone f → totalInfluence p f ≤ K →
      ∃ (J : Finset (Fin n)) (u : Cube (Fin n) → Bool),
        J.card ≤ M ∧ Monotone u ∧ IsJuntaOn J u ∧ error p f u ≤ ε

section Representation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem indicator_monotone {A : Set (Cube ι)} (hA : Monotone (fun x => x ∈ A)) :
    Monotone (fun x => decide (x ∈ A)) := by
  intro x y hxy
  by_cases hx : x ∈ A
  · simp [hx, hA hxy hx]
  · simp [hx]

/-- A positive DNF yields exactly the increasing family and minimal-element
bound appearing in the set-form conjecture. -/
theorem family_of_dnf (A : Set (Cube ι)) (p ε : ℝ) (k : ℕ)
    (terms : Finset (Finset ι)) (hwidth : ∀ T ∈ terms, T.card ≤ k)
    (herr : error p (fun x => decide (x ∈ A)) (evalDNF terms) ≤ ε) :
    ∃ B : Set (Cube ι), Monotone (fun x => x ∈ B) ∧
      probability p (fun x => (x ∈ A) ≠ (x ∈ B)) ≤ ε ∧
      ∀ z, MinimalAccepted (fun x => x ∈ B) z → (support z).card ≤ k := by
  refine ⟨{x | DNFHolds terms x}, dnfHolds_mono terms, ?_, ?_⟩
  · have heq : probability p (fun x => (x ∈ A) ≠ DNFHolds terms x) =
        error p (fun x => decide (x ∈ A)) (evalDNF terms) := by
      unfold probability error evalDNF
      apply congrArg (expectation p)
      funext x
      by_cases hx : x ∈ A <;> by_cases hg : DNFHolds terms x <;> simp [hx,hg]
    exact heq.trans_le herr
  · exact fun z hz => minimal_dnf_support_card_le terms k hwidth hz

omit [Fintype ι] [DecidableEq ι] in
theorem constant_dnf (b : Bool) :
    ∃ terms : Finset (Finset ι), (∀ T ∈ terms, T.card ≤ 0) ∧
      evalDNF terms = fun _ => b := by
  cases b
  · refine ⟨∅, by simp, ?_⟩
    funext x
    simp [evalDNF, DNFHolds]
  · refine ⟨{∅}, by simp, ?_⟩
    funext x
    simp [evalDNF, DNFHolds, TermHolds]

end Representation

/-- Exact all-bias assembly. This theorem is intentionally conditional until
the two named structural input propositions have been proved separately. -/
theorem friedgutAllBias_of_lowBias_and_compactJunta
    (hlow : NarrowDNFApproximation) (hjunta : CompactBiasMonotoneJunta) :
    FriedgutAllBias := by
  obtain ⟨C₀, hC₀, hlow⟩ := hlow
  intro c ε hc hε hε1
  let lam := ε/(2*c)
  have hlam0 : 0 < lam := div_pos hε (mul_pos (by norm_num) hc)
  have hcompact : ∃ M : ℕ, ∀ (n : ℕ) (p : ℝ), lam ≤ p → p ≤ 1-lam →
      ∀ f : Cube (Fin n) → Bool, Monotone f → totalInfluence p f ≤ c →
      ∃ (J : Finset (Fin n)) (u : Cube (Fin n) → Bool),
        J.card ≤ M ∧ Monotone u ∧ IsJuntaOn J u ∧ error p f u ≤ ε := by
    by_cases hlam : lam ≤ 1/2
    · exact hjunta lam c ε hlam0 hlam hc hε hε1
    · refine ⟨0, ?_⟩
      intro n p hp0 hp1
      exact False.elim (by linarith)
  obtain ⟨M, hM⟩ := hcompact
  let lowBound := Real.exp (C₀*(2*c+1)^2/ε^2)
  let lowWidth : ℕ := Nat.ceil lowBound
  refine ⟨max lowWidth M, ?_⟩
  intro p hp0 hp1 n hn A hA hboundary
  let f : Cube (Fin n) → Bool := fun x => decide (x ∈ A)
  have hf : Monotone f := indicator_monotone hA
  have hIidentity := totalInfluence_eq_sensitivity p f
  have hboundary' : p * expectation p (sensitivity f) ≤ c := hboundary
  have hresampling : totalInfluence p f ≤ 2*(1-p)*c := by
    have h := mul_le_mul_of_nonneg_left hboundary'
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sub_nonneg.mpr hp1.le))
    nlinarith
  by_cases hlowp : p ≤ 1/2
  · have hIf : totalInfluence p f ≤ 2*c := by
      nlinarith [mul_nonneg hp0.le hc.le]
    obtain ⟨terms, hwidth, herr⟩ := hlow n hn (2*c) p ε
      (by positivity) hp0 hlowp hε hε1 f hf hIf
    apply family_of_dnf A p ε (max lowWidth M) terms _ herr
    intro T hT
    have hTreal : (T.card : ℝ) ≤ lowBound := hwidth T hT
    have hTnat : T.card ≤ lowWidth := by
      exact_mod_cast hTreal.trans (Nat.le_ceil lowBound)
    exact hTnat.trans (le_max_left _ _)
  · by_cases hnear : 1-p ≤ lam
    · obtain ⟨b, hb⟩ := near_one_constant_approximation hp0 hp1 hc f hboundary' hnear
      obtain ⟨terms, hwidth, heval⟩ := constant_dnf (ι := Fin n) b
      apply family_of_dnf A p ε (max lowWidth M) terms
      · intro T hT
        exact (hwidth T hT).trans (Nat.zero_le _)
      · simpa only [heval] using hb
    · have hplam : lam ≤ p := by linarith
      have hpupper : p ≤ 1-lam := by linarith
      have hIf : totalInfluence p f ≤ c := by
        have := mul_nonneg (show (0:ℝ) ≤ 2*p-1 by linarith) hc.le
        nlinarith
      obtain ⟨J,u,hJ,hu,hlocal,herr⟩ := hM n p hplam hpupper f hf hIf
      obtain ⟨terms,hwidth,heval⟩ := monotone_junta_eq_dnf J hu hlocal
      apply family_of_dnf A p ε (max lowWidth M) terms
      · intro T hT
        exact (hwidth T hT).trans (hJ.trans (le_max_right _ _))
      · simpa only [heval] using herr

end NarrowDNF
