import NarrowDNF.Influence
import NarrowDNF.ActivationLoad
import NarrowDNF.MinimalElements
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring

/-! Exact formal target propositions for the headline results. These definitions
are not axioms. Their unconditional proofs are provided in `Paper.lean`. -/
noncomputable section
namespace NarrowDNF
attribute [local instance] Classical.propDecidable

/-- Boolean evaluation of any finite positive DNF, with the conventional empty
conjunction and empty disjunction already supplied by `DNFHolds`. -/
def evalDNF {ι : Type*} (terms : Finset (Finset ι)) (x : Cube ι) : Bool :=
  decide (DNFHolds terms x)

/-- Exact target for Theorem 1.2. The absolute constant is quantified before
all dimensions, influence bounds, biases, errors and functions. -/
def NarrowDNFApproximation : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ K p ε : ℝ,
    0 < K → 0 < p → p ≤ 1/2 → 0 < ε → ε < 1 →
    ∀ f : Cube (Fin n) → Bool, Monotone f → Influence.totalInfluence p f ≤ K →
    ∃ terms : Finset (Finset (Fin n)),
      (∀ T ∈ terms, (T.card : ℝ) ≤ Real.exp (C * (K+1)^2 / ε^2)) ∧
      ProductMeasure.error p f (evalDNF terms) ≤ ε

/-- Exact simultaneous approximation, increasing-locality, arity and
multiplicity-load target for Lemma 2.1. This is not a hypothesis silently
imported into the final theorem. -/
def HatamiArityLoad : Prop :=
  ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1/2 → ∀ (f : Cube (Fin n) → Bool) (a : ℝ),
    0 < a → a ≤ 1 →
    let C : ℕ := Nat.ceil (Influence.totalInfluence p f)
    let d : ℕ := Nat.ceil (1000 * (C : ℝ) / a)
    let L : ℝ := Real.exp (10000000000 * (C : ℝ)^2 / a^2)
    ∃ (J : Activation (Fin n)) (h : Cube (Fin n) → Bool),
      J.Increasing ∧ ProductMeasure.error p f h ≤ a ∧ J.Measurable h ∧
      J.ArityLE d ∧ J.load p ≤ L

/-- Exact all-bias target, using the stronger relative-boundary hypothesis,
not an all-bias resampling-influence hypothesis. -/
def FriedgutAllBias : Prop :=
  ∀ c ε : ℝ, 0 < c → 0 < ε → ε < 1 → ∃ k : ℕ,
    ∀ p : ℝ, 0 < p → p < 1 → ∀ n : ℕ, 1 ≤ n →
    ∀ A : Set (Cube (Fin n)), Monotone (fun x => x ∈ A) →
      p * ProductMeasure.expectation p (Influence.sensitivity (fun x => decide (x ∈ A))) ≤ c →
    ∃ B : Set (Cube (Fin n)), Monotone (fun x => x ∈ B) ∧
      ProductMeasure.probability p (fun x => (x ∈ A) ≠ (x ∈ B)) ≤ ε ∧
      ∀ z, MinimalAccepted (fun x => x ∈ B) z → (support z).card ≤ k

end NarrowDNF
