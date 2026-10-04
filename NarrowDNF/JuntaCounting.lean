import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Finite counting and spectral-mass estimates in Friedgut's junta argument.
All analytic estimates are explicit hypotheses of these intermediate lemmas. -/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.JuntaCounting
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Damped coefficient mass seen by one coordinate. -/
def stableEnergy (θ : ℝ) (e : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ S : Finset ι, if i ∈ S then θ^S.card * e S else 0

/-- Coordinates whose pivotal probability exceeds a squared cutoff. -/
def selected (τ : ℝ) (P : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => τ^2 ≤ P i)

omit [DecidableEq ι] in
@[simp] theorem mem_selected (τ : ℝ) (P : ι → ℝ) (i : ι) :
    i ∈ selected τ P ↔ τ^2 ≤ P i := by simp [selected]

omit [DecidableEq ι] in
theorem selected_card_bound (τ L : ℝ) (hτ : 0 < τ) (P : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hL : ∑ i, P i ≤ L) :
    ((selected τ P).card : ℝ) ≤ L / τ^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
  calc
    ((selected τ P).card : ℝ)*τ^2 = ∑ i ∈ selected τ P, τ^2 := by simp
    _ ≤ ∑ i ∈ selected τ P, P i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (mem_selected τ P i).mp hi
    _ ≤ ∑ i, P i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro i _ _
      exact hP i)
    _ ≤ L := hL

theorem stableEnergy_nonneg (θ : ℝ) (hθ : 0 ≤ θ) (e : Finset ι → ℝ)
    (he : ∀ S, 0 ≤ e S) (i : ι) : 0 ≤ stableEnergy θ e i := by
  unfold stableEnergy
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact mul_nonneg (pow_nonneg hθ _) (he S)
  · rfl

/-- A squared stable-energy estimate becomes a linear estimate below the cutoff. -/
theorem stableEnergy_le_cutoff (θ τ : ℝ) (hθ : 0 ≤ θ) (hτ : 0 ≤ τ)
    (e : Finset ι → ℝ) (he : ∀ S, 0 ≤ e S) (P : ι → ℝ) (hP : ∀ i, 0 ≤ P i)
    (hstable : ∀ i, (stableEnergy θ e i)^2 ≤ (P i)^3) (i : ι)
    (hi : i ∉ selected τ P) : stableEnergy θ e i ≤ τ*P i := by
  have hcut : P i ≤ τ^2 := le_of_lt (lt_of_not_ge (by simpa using hi))
  have hmul := mul_le_mul_of_nonneg_right hcut (sq_nonneg (P i))
  have hpos := mul_nonneg hτ (hP i)
  have hepos := stableEnergy_nonneg θ hθ e he i
  have hh := hstable i
  nlinarith [sq_nonneg (stableEnergy θ e i-τ*P i)]

/-- Every low-degree coefficient outside the selected coordinates is charged
to a small-influence coordinate in its support. -/
theorem lowDegree_outside_bound (θ τ L : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hτ : 0 ≤ τ) (k : ℕ) (J : Finset ι) (e : Finset ι → ℝ) (he : ∀ S, 0 ≤ e S)
    (P : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hL : ∑ i, P i ≤ L)
    (hstable : ∀ i, i ∉ J → stableEnergy θ e i ≤ τ*P i) :
    (∑ S : Finset ι, if S.card ≤ k ∧ ¬ S ⊆ J then e S else 0) ≤ τ*L/θ^k := by
  apply (le_div_iff₀ (pow_pos hθ0 k)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ S : Finset ι, ∑ i : ι, if i ∉ J ∧ i ∈ S then θ^S.card*e S else 0 := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hgood : S.card ≤ k ∧ ¬ S ⊆ J
      · simp only [if_pos hgood]
        obtain ⟨i,hiS,hiJ⟩ := Finset.not_subset.mp hgood.2
        have hterm : θ^S.card*e S ≤
            ∑ j : ι, if j ∉ J ∧ j ∈ S then θ^S.card*e S else 0 := by
          simpa [hiS,hiJ] using Finset.single_le_sum (f := fun j : ι =>
            if j ∉ J ∧ j ∈ S then θ^S.card*e S else 0)
            (fun j _ => by
              dsimp only
              split_ifs
              · exact mul_nonneg (pow_nonneg hθ0.le _) (he S)
              · rfl) (Finset.mem_univ i)
        have hpow : e S*θ^k ≤ θ^S.card*e S := by
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0.le hθ1 hgood.1) (he S)
        exact hpow.trans hterm
      · simp only [if_neg hgood, zero_mul]
        apply Finset.sum_nonneg
        intro i _
        split_ifs
        · exact mul_nonneg (pow_nonneg hθ0.le _) (he S)
        · rfl
    _ = ∑ i : ι, if i ∉ J then stableEnergy θ e i else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∉ J
      · simp [hi, stableEnergy]
      · simp [hi]
    _ ≤ ∑ i : ι, τ*P i := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∉ J
      · simpa only [if_pos hi] using hstable i hi
      · simpa only [if_neg hi] using mul_nonneg hτ (hP i)
    _ ≤ τ*L := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hL hτ

/-- Split all omitted coefficient mass into its low-degree and high-degree parts. -/
theorem outside_mass_le_split (k : ℕ) (J : Finset ι) (e : Finset ι → ℝ)
    (he : ∀ S, 0 ≤ e S) :
    (∑ S : Finset ι, if S ⊆ J then 0 else e S) ≤
      (∑ S : Finset ι, if S.card ≤ k ∧ ¬ S ⊆ J then e S else 0) +
        ∑ S ∈ Finset.univ.filter (fun S : Finset ι => k < S.card), e S := by
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  by_cases hSJ : S ⊆ J <;> by_cases hcard : S.card ≤ k
  all_goals first
    | simp [hSJ,hcard,not_lt_of_ge hcard]
    | simp [hSJ,hcard,lt_of_not_ge hcard,he S]

end NarrowDNF.JuntaCounting
