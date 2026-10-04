import NarrowDNF.Fourier
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-!
# Finite combinatorial part of Bourgain's component estimate

The definitions use the actual biased Fourier components. The pointwise
lemmas below are independent of any analytic square-function hypothesis.
They are ingredients, not a claim to have proved Hatami (11) or (18).
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainComponents

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared mass of components of degree at most k whose pointwise values are
small. The empty support is included, exactly as in Hatami's displayed sum. -/
def smallComponentMass (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (η : ℝ) : ℝ :=
  ProductMeasure.expectation p (fun x =>
    ∑ S ∈ (Finset.univ.filter fun S : Finset ι => S.card ≤ k),
      if |Fourier.component p f S x| ≤ η then Fourier.component p f S x ^ 2 else 0)

/-- The coordinate square function, before taking a square root. -/
def coordinateSquare (F : Finset (Finset ι)) (c : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ S ∈ F, if i ∈ S then c S ^ 2 else 0

/-- Pointwise truncated mass of an arbitrary family of components. -/
def truncatedMass (F : Finset (Finset ι)) (c : Finset ι → ℝ) (η : ℝ) : ℝ :=
  ∑ S ∈ F, if |c S| ≤ η then c S ^ 2 else 0

/-- The coordinates with a square function exceeding the threshold. -/
def largeCoordinates (F : Finset (Finset ι)) (c : Finset ι → ℝ) (τ : ℝ) : Finset ι :=
  Finset.univ.filter fun i => τ ^ 2 < coordinateSquare F c i

omit [Fintype ι] [DecidableEq ι] in
/-- A simple polynomial bound for the geometric sum. -/
theorem sum_powers_le (n k : ℕ) : (∑ j ∈ Finset.range (k+1), n^j) ≤ (n+1)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ (n+1)^k + n^(k+1) := Nat.add_le_add_right ih _
      _ ≤ (n+1)^k + n * (n+1)^k := by
        apply Nat.add_le_add_left
        rw [pow_succ, mul_comm]
        exact Nat.mul_le_mul_left n (Nat.pow_le_pow_left (Nat.le_succ n) k)
      _ = (n+1)^(k+1) := by ring

omit [Fintype ι] in
/-- Count subsets of A of size at most k. The extra one handles the empty set
and makes the estimate valid even when A is empty. -/
theorem card_small_subsets_le (A : Finset ι) (k : ℕ) :
    (A.powerset.filter fun S => S.card ≤ k).card ≤ (A.card+1)^k := by
  classical
  have hsub : (A.powerset.filter fun S => S.card ≤ k) ⊆
      (Finset.range (k+1)).biUnion (fun j => A.powersetCard j) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    apply Finset.mem_biUnion.mpr
    exact ⟨S.card, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hS.2),
      Finset.mem_powersetCard.mpr ⟨hS.1,rfl⟩⟩
  calc
    _ ≤ ((Finset.range (k+1)).biUnion (fun j => A.powersetCard j)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (k+1), (A.powersetCard j).card := Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (k+1), A.card.choose j := by simp
    _ ≤ ∑ j ∈ Finset.range (k+1), A.card^j :=
      Finset.sum_le_sum fun j _ => Nat.choose_le_pow _ _
    _ ≤ (A.card+1)^k := sum_powers_le _ _

omit [Fintype ι] in
theorem coordinateSquare_nonneg (F : Finset (Finset ι)) (c : Finset ι → ℝ) (i : ι) :
    0 ≤ coordinateSquare F c i := by
  apply Finset.sum_nonneg
  intro S _
  split_ifs <;> first | exact le_rfl | positivity

/-- Double counting of coordinate incidence, pointwise. -/
theorem sum_coordinateSquare (F : Finset (Finset ι)) (c : Finset ι → ℝ) :
    (∑ i, coordinateSquare F c i) = ∑ S ∈ F, (S.card : ℝ) * c S ^ 2 := by
  unfold coordinateSquare
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp

/-- A component not supported entirely on A is charged to a coordinate outside A. -/
theorem uncovered_mass_le (F : Finset (Finset ι)) (c : Finset ι → ℝ) (A : Finset ι) :
    (∑ S ∈ F, if S ⊆ A then 0 else c S ^ 2) ≤
      ∑ i, if i ∈ A then 0 else coordinateSquare F c i := by
  classical
  have hexpand : (∑ i, if i ∈ A then 0 else coordinateSquare F c i) =
      ∑ S ∈ F, ∑ i, if i ∈ A then 0 else if i ∈ S then c S ^ 2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ A <;> simp [hi, coordinateSquare]
  rw [hexpand]
  apply Finset.sum_le_sum
  intro S _
  by_cases hSA : S ⊆ A
  · simp only [if_pos hSA]
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> first | exact le_rfl | positivity
  · simp only [if_neg hSA]
    obtain ⟨i, hiS, hiA⟩ := Finset.not_subset.mp hSA
    calc
      c S ^ 2 = (if i ∈ A then 0 else if i ∈ S then c S ^ 2 else 0) := by
        simp [hiA,hiS]
      _ ≤ ∑ i, if i ∈ A then 0 else if i ∈ S then c S ^ 2 else 0 := by
        apply Finset.single_le_sum _ (Finset.mem_univ i)
        intro j _
        split_ifs <;> first | exact le_rfl | positivity

/-- The truncated square is bounded by the truncation level squared. -/
theorem truncated_square_le (a η : ℝ) : (if |a| ≤ η then a^2 else 0) ≤ η^2 := by
  split_ifs with h
  · have h' := abs_le.mp h
    nlinarith [sq_abs a]
  · positivity

omit [Fintype ι] in
/-- The mass of components entirely supported on A has a polynomial cardinality
bound. No probabilistic or analytic assumption enters this step. -/
theorem contained_truncated_mass_le (F : Finset (Finset ι)) (c : Finset ι → ℝ)
    (A : Finset ι) (k : ℕ) (hF : ∀ S ∈ F, S.card ≤ k) (η : ℝ) :
    (∑ S ∈ F, if S ⊆ A then (if |c S| ≤ η then c S ^ 2 else 0) else 0) ≤
      ((A.card+1 : ℕ) : ℝ)^k * η^2 := by
  classical
  rw [← Finset.sum_filter]
  have hcard : (F.filter fun S => S ⊆ A).card ≤ (A.card+1)^k := by
    refine le_trans (Finset.card_le_card ?_) (card_small_subsets_le A k)
    intro S hS
    simp only [Finset.mem_filter] at hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS.2, hF S hS.1⟩
  calc
    _ ≤ ∑ S ∈ F.filter (fun S => S ⊆ A), η^2 :=
      Finset.sum_le_sum fun S _ => truncated_square_le _ _
    _ = ((F.filter fun S => S ⊆ A).card : ℝ) * η^2 := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg η)
      exact_mod_cast hcard

/-- Split truncated component mass between covered supports and uncovered
coordinates. -/
theorem truncated_mass_split (F : Finset (Finset ι)) (c : Finset ι → ℝ)
    (A : Finset ι) (k : ℕ) (hF : ∀ S ∈ F, S.card ≤ k) (η : ℝ) :
    truncatedMass F c η ≤ ((A.card+1 : ℕ) : ℝ)^k * η^2 +
      ∑ i, if i ∈ A then 0 else coordinateSquare F c i := by
  have hsplit : truncatedMass F c η ≤
      (∑ S ∈ F, if S ⊆ A then (if |c S| ≤ η then c S ^ 2 else 0) else 0) +
      ∑ S ∈ F, if S ⊆ A then 0 else c S ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro S _
    by_cases hSA : S ⊆ A
    · simp [hSA]
    · simp only [if_neg hSA, zero_add]
      split_ifs <;> first | exact le_rfl | positivity
  exact hsplit.trans (add_le_add (contained_truncated_mass_le F c A k hF η)
    (uncovered_mass_le F c A))

/-- Full pointwise three-piece Bourgain decomposition, with an integer
large-coordinate cutoff M. -/
theorem pointwise_bourgain_split (F : Finset (Finset ι)) (c : Finset ι → ℝ)
    (k M : ℕ) (hF : ∀ S ∈ F, S.card ≤ k) (η τ : ℝ) :
    truncatedMass F c η ≤ (M : ℝ)^k * η^2 +
      (∑ i, if coordinateSquare F c i ≤ τ^2 then coordinateSquare F c i else 0) +
      (if M ≤ (largeCoordinates F c τ).card then ∑ S ∈ F, c S^2 else 0) := by
  classical
  let A := largeCoordinates F c τ
  have hsmall : (∑ i, if i ∈ A then 0 else coordinateSquare F c i) =
      ∑ i, if coordinateSquare F c i ≤ τ^2 then coordinateSquare F c i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [A, largeCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : coordinateSquare F c i ≤ τ^2
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  by_cases hM : M ≤ A.card
  · have hbound : truncatedMass F c η ≤ ∑ S ∈ F, c S^2 := by
      apply Finset.sum_le_sum
      intro S _
      split_ifs <;> first | exact le_rfl | positivity
    have hnonneg : 0 ≤ ∑ i, if coordinateSquare F c i ≤ τ^2 then coordinateSquare F c i else 0 := by
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact coordinateSquare_nonneg F c i
      · exact le_rfl
    have hnonneg' : 0 ≤ (M : ℝ)^k * η^2 := by positivity
    change M ≤ (largeCoordinates F c τ).card at hM
    rw [if_pos hM]
    linarith
  · have hcard : A.card + 1 ≤ M := by omega
    have hpow : ((A.card+1 : ℕ) : ℝ)^k ≤ (M : ℝ)^k := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast hcard
    have h := (truncated_mass_split F c A k hF η).trans
      (add_le_add_right (mul_le_mul_of_nonneg_right hpow (sq_nonneg η)) _)
    rw [hsmall] at h
    change ¬ M ≤ (largeCoordinates F c τ).card at hM
    simpa only [if_neg hM, add_zero] using h

/-- The large-coordinate count is bounded pointwise by the total coordinate
square mass. This is the unintegrated Markov step. -/
theorem largeCoordinates_count_le (F : Finset (Finset ι)) (c : Finset ι → ℝ) (τ : ℝ) :
    τ^2 * ((largeCoordinates F c τ).card : ℝ) ≤ ∑ i, coordinateSquare F c i := by
  classical
  calc
    _ = ∑ i, if i ∈ largeCoordinates F c τ then τ^2 else 0 := by
      simp [mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact le_of_lt ((Finset.mem_filter.mp hi).2)
      · exact coordinateSquare_nonneg F c i

end NarrowDNF.BourgainComponents
