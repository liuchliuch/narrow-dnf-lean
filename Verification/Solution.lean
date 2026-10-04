import NarrowDNF.Paper

/-! Proofs of the separately reviewed paper statements.
This file does not import the challenge or its independent model. -/
noncomputable section
namespace NarrowDNF.Verification
attribute [local instance] Classical.propDecidable

/-- Theorem 1.2. The absolute constant precedes dimension and bias. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ K p ε : ℝ,
      0 < K → 0 < p → p ≤ 1/2 → 0 < ε → ε < 1 →
      ∀ f : Cube (Fin n) → Bool, Monotone f → Influence.totalInfluence p f ≤ K →
      ∃ terms : Finset (Finset (Fin n)),
        (∀ T ∈ terms, (T.card : ℝ) ≤ Real.exp (C * (K+1)^2 / ε^2)) ∧
        ProductMeasure.error p f (evalDNF terms) ≤ ε := _root_.NarrowDNF.main_narrow_dnf

/-- Lemma 2.1. All properties hold for the same activation family and decoder. -/
theorem lemma_2_1 :
    ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1/2 → ∀ (f : Cube (Fin n) → Bool) (a : ℝ),
      0 < a → a ≤ 1 →
      let C : ℕ := Nat.ceil (Influence.totalInfluence p f)
      let d : ℕ := Nat.ceil (1000 * (C : ℝ) / a)
      let L : ℝ := Real.exp (10000000000 * (C : ℝ)^2 / a^2)
      ∃ (J : Activation (Fin n)) (h : Cube (Fin n) → Bool),
        J.Increasing ∧ ProductMeasure.error p f h ≤ a ∧ J.Measurable h ∧
        J.ArityLE d ∧ J.load p ≤ L := _root_.NarrowDNF.hatami_arity_load

/-- Conjecture 1.1, proved. The hypothesis is the relative boundary. -/
theorem conjecture_1_1 :
    ∀ c ε : ℝ, 0 < c → 0 < ε → ε < 1 → ∃ k : ℕ,
      ∀ p : ℝ, 0 < p → p < 1 → ∀ n : ℕ, 1 ≤ n →
      ∀ A : Set (Cube (Fin n)), Monotone (fun x => x ∈ A) →
        p * ProductMeasure.expectation p (Influence.sensitivity (fun x => decide (x ∈ A))) ≤ c →
      ∃ B : Set (Cube (Fin n)), Monotone (fun x => x ∈ B) ∧
        ProductMeasure.probability p (fun x => (x ∈ A) ≠ (x ∈ B)) ≤ ε ∧
        ∀ z, MinimalAccepted (fun x => x ∈ B) z → (support z).card ≤ k := _root_.NarrowDNF.friedgut_all_bias

end NarrowDNF.Verification
