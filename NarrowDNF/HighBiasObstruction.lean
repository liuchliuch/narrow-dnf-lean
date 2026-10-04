import NarrowDNF.MainStatements
import NarrowDNF.Russo
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

/-!
# The exact high-bias AND obstruction

Appendix B's sequence is retained exactly: `p_n = 1 - 1/n`, with the
Boolean AND on `Fin n`. Probabilities and resampling influences refer to
the finite product definitions used throughout the development.
-/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace NarrowDNF.HighBiasObstruction

open ProductMeasure Influence
attribute [local instance] Classical.propDecidable

section FiniteCube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def andAll (x : Cube ι) : Bool := decide (∀ i, x i = true)

omit [DecidableEq ι] in
@[simp] theorem andAll_eq_true (x : Cube ι) : andAll x = true ↔ ∀ i, x i = true := by
  simp [andAll]

omit [DecidableEq ι] in
theorem andAll_monotone : Monotone (andAll : Cube ι → Bool) := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  intro hx
  apply (andAll_eq_true y).mpr
  intro i
  exact Bool.eq_true_of_true_le (by simpa [(andAll_eq_true x).mp hx i] using hxy i)

theorem probability_all_true (p : ℝ) :
    probability p (fun x : Cube ι => ∀ i, x i = true) = p ^ Fintype.card ι := by
  have hp (x : Cube ι) : (∀ i, x i = true) ↔ x = fun _ => true := by
    constructor
    · exact funext
    · intro h
      simp [h]
  unfold probability expectation
  simp_rw [hp]
  simp [mul_ite, weight]

theorem andAll_mean (p : ℝ) :
    expectation p (fun x : Cube ι => boolValue (andAll x)) = p ^ Fintype.card ι := by
  simpa only [probability, boolValue, andAll, decide_eq_true_eq] using
    probability_all_true (ι := ι) p

theorem andAll_probability (p : ℝ) :
    probability p (fun x : Cube ι => andAll x = true) = p ^ Fintype.card ι := by
  simpa only [andAll_eq_true] using probability_all_true (ι := ι) p

/-- The expected bit-flip sensitivity of AND, from the established Russo identity. -/
theorem andAll_sensitivity (p : ℝ) :
    expectation p (sensitivity (andAll : Cube ι → Bool)) =
      (Fintype.card ι : ℝ) * p ^ (Fintype.card ι - 1) := by
  have h := Russo.monotone_expectation_hasDerivAt p (andAll : Cube ι → Bool) andAll_monotone
  have hfun : (fun q => expectation q (fun x : Cube ι => boolValue (andAll x))) =
      (fun q : ℝ => q ^ Fintype.card ι) := funext andAll_mean
  rw [hfun] at h
  have hd : HasDerivAt (fun q : ℝ => q ^ Fintype.card ι)
      ((Fintype.card ι : ℝ) * p ^ (Fintype.card ι - 1)) p := by
    simpa using (hasDerivAt_id p).pow (Fintype.card ι)
  exact h.unique hd

theorem andAll_totalInfluence (p : ℝ) :
    totalInfluence p (andAll : Cube ι → Bool) =
      2 * p * (1-p) * (Fintype.card ι : ℝ) * p ^ (Fintype.card ι - 1) := by
  rw [totalInfluence_eq_sensitivity, andAll_sensitivity]
  ring

theorem probability_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q : Cube ι → Prop} (hPQ : ∀ x, P x → Q x) :
    probability p P ≤ probability p Q := by
  apply expectation_mono hp0 hp1
  intro x
  by_cases hP : P x <;> by_cases hQ : Q x <;> simp_all

theorem term_probability (p : ℝ) (T : Finset ι) :
    probability p (TermHolds T) = p^T.card := by
  calc
    _ = expectation p (fun x : Cube ι =>
        (fun z : T → Bool => if ∀ i, z i = true then (1 : ℝ) else 0) (fun i => x i)) := by
      unfold probability
      congr 1
      funext x
      simp [TermHolds]
    _ = expectation p (fun z : T → Bool => if ∀ i, z i = true then (1 : ℝ) else 0) := by
      have h := expectation_restrict (ι := ι) p (fun i : ι => i ∈ T)
        (fun z : {i // i ∈ T} → Bool => if ∀ i, z i = true then (1 : ℝ) else 0)
      convert h using 1
      congr 1
      exact Subsingleton.elim _ _
    _ = _ := by simpa only [probability, Fintype.card_coe] using probability_all_true (ι := T) p

theorem nonempty_dnf_mean_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (terms : Finset (Finset ι)) (hne : terms.Nonempty) (w : ℕ)
    (hw : ∀ T ∈ terms, T.card ≤ w) :
    p^w ≤ expectation p (fun x => boolValue (evalDNF terms x)) := by
  obtain ⟨T, hT⟩ := hne
  calc
    p^w ≤ p^T.card := pow_le_pow_of_le_one hp0 hp1 (hw T hT)
    _ = probability p (TermHolds T) := (term_probability p T).symm
    _ ≤ probability p (DNFHolds terms) :=
      probability_mono hp0 hp1 (fun x hx => ⟨T, hT, hx⟩)
    _ = _ := by simp [probability, boolValue, evalDNF]

omit [DecidableEq ι] in
theorem andAll_le_nonempty_dnf (terms : Finset (Finset ι)) (hne : terms.Nonempty) :
    (andAll : Cube ι → Bool) ≤ evalDNF terms := by
  obtain ⟨T, hT⟩ := hne
  intro x
  apply Bool.le_iff_imp.mpr
  intro hx
  apply decide_eq_true
  exact ⟨T, hT, fun i _ => (andAll_eq_true x).mp hx i⟩

theorem error_eq_mean_sub (p : ℝ) (f g : Cube ι → Bool) (hfg : f ≤ g) :
    error p f g = expectation p (fun x => boolValue (g x)) -
      expectation p (fun x => boolValue (f x)) := by
  unfold error probability
  calc
    _ = expectation p (fun x => boolValue (g x) - boolValue (f x)) := by
      congr 1
      funext x
      have h := hfg x
      cases hfx : f x <;> cases hgx : g x <;>
        simp_all [boolValue, Bool.le_iff_imp]
    _ = _ := by simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem nonempty_dnf_error_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (terms : Finset (Finset ι)) (hne : terms.Nonempty) (w : ℕ)
    (hw : ∀ T ∈ terms, T.card ≤ w) :
    p^w - p^Fintype.card ι ≤ error p (andAll : Cube ι → Bool) (evalDNF terms) := by
  rw [error_eq_mean_sub p _ _ (andAll_le_nonempty_dnf terms hne), andAll_mean]
  exact sub_le_sub_right (nonempty_dnf_mean_ge hp0 hp1 terms hne w hw) _

theorem empty_dnf_error (p : ℝ) :
    error p (andAll : Cube ι → Bool) (evalDNF (∅ : Finset (Finset ι))) = p^Fintype.card ι := by
  have hzero : evalDNF (∅ : Finset (Finset ι)) = fun _ => false := by
    funext x
    simp [evalDNF, DNFHolds]
  rw [hzero, error_symm, error_eq_mean_sub p _ _ (fun _ => Bool.false_le _), andAll_mean]
  simp [boolValue]

end FiniteCube

/-- The exact sequence in Appendix B, without a reparameterization. -/
def bias (n : ℕ) : ℝ := 1 - 1 / (n : ℝ)

def andFunction (n : ℕ) : Cube (Fin n) → Bool := andAll

def relativeBoundary (p : ℝ) {n : ℕ} (f : Cube (Fin n) → Bool) : ℝ :=
  p * expectation p (sensitivity f)

theorem bias_pos {n : ℕ} (hn : 2 ≤ n) : 0 < bias n := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  unfold bias
  have h : 1 / (n : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith

theorem bias_lt_one {n : ℕ} (hn : 2 ≤ n) : bias n < 1 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold bias
  have h : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnreal
  linarith

theorem andFunction_probability (n : ℕ) :
    probability (bias n) (fun x => andFunction n x = true) = (bias n)^n := by
  simpa only [andFunction, Fintype.card_fin] using andAll_probability (ι := Fin n) (bias n)

theorem andFunction_totalInfluence {n : ℕ} (hn : 2 ≤ n) :
    totalInfluence (bias n) (andFunction n) = 2 * (bias n)^n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpow : (bias n)^n = (bias n)^(n-1) * bias n := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n by omega)]
  have hb : (1-bias n) * (n : ℝ) = 1 := by unfold bias; field_simp; ring
  rw [andFunction, andAll_totalInfluence, Fintype.card_fin]
  calc
    _ = 2 * ((1-bias n) * (n : ℝ)) * ((bias n)^(n-1) * bias n) := by ring
    _ = _ := by rw [hb, ← hpow]; ring

theorem andFunction_relativeBoundary {n : ℕ} (hn : 2 ≤ n) :
    relativeBoundary (bias n) (andFunction n) = (n : ℝ) * (bias n)^n := by
  have hpow : (bias n)^n = (bias n)^(n-1) * bias n := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n by omega)]
  unfold relativeBoundary andFunction
  rw [andAll_sensitivity, Fintype.card_fin, hpow]
  ring

theorem andFunction_totalInfluence_le_two {n : ℕ} (hn : 2 ≤ n) :
    totalInfluence (bias n) (andFunction n) ≤ 2 := by
  rw [andFunction_totalInfluence hn]
  nlinarith [pow_le_one₀ (bias_pos hn).le (bias_lt_one hn).le (n := n)]

/-- The original parameter sequence approaches one. -/
theorem bias_tendsto_one : Tendsto bias atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 1)
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [one_div, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hi

/-- The exact AND acceptance sequence tends to `e⁻¹`. -/
theorem mass_tendsto_exp_neg_one :
    Tendsto (fun n : ℕ => (bias n)^n) atTop (𝓝 (Real.exp (-1))) := by
  simpa [bias, sub_eq_add_neg, neg_div] using Real.tendsto_one_add_div_pow_exp (-1)

theorem andFunction_probability_tendsto :
    Tendsto (fun n : ℕ => probability (bias n) (fun x => andFunction n x = true))
      atTop (𝓝 (Real.exp (-1))) := by
  simpa only [andFunction_probability] using mass_tendsto_exp_neg_one

/-- Fixed-width conjunctions have acceptance probability tending to one. -/
theorem fixed_power_tendsto_one (w : ℕ) :
    Tendsto (fun n : ℕ => (bias n)^w) atTop (𝓝 1) := by
  simpa using bias_tendsto_one.pow w

theorem andFunction_totalInfluence_tendsto :
    Tendsto (fun n : ℕ => totalInfluence (bias n) (andFunction n))
      atTop (𝓝 (2 / Real.exp 1)) := by
  have h : Tendsto (fun n : ℕ => 2 * (bias n)^n)
      atTop (𝓝 (2 * Real.exp (-1))) := tendsto_const_nhds.mul mass_tendsto_exp_neg_one
  have h' : Tendsto (fun n : ℕ => totalInfluence (bias n) (andFunction n))
      atTop (𝓝 (2 * Real.exp (-1))) := h.congr' (by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (andFunction_totalInfluence hn).symm)
  simpa [Real.exp_neg, div_eq_mul_inv] using h'

/-- The all-bias relative-boundary quantity diverges along this example. -/
theorem andFunction_relativeBoundary_tendsto_atTop :
    Tendsto (fun n : ℕ => relativeBoundary (bias n) (andFunction n)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) * (bias n)^n) atTop atTop :=
    Tendsto.atTop_mul_pos (Real.exp_pos (-1)) tendsto_natCast_atTop_atTop
      mass_tendsto_exp_neg_one
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (andFunction_relativeBoundary hn).symm

theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1/2 := by
  have ht : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  simpa [Real.exp_neg, one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) ht

/-- For every fixed width and every `ε < e⁻¹`, eventually every positive DNF
of that width has error strictly greater than `ε`. The empty DNF is included. -/
theorem eventually_every_dnf_error_gt (w : ℕ) {ε : ℝ} (_hε0 : 0 < ε)
    (hε : ε < 1 / Real.exp 1) :
    ∀ᶠ n : ℕ in atTop, ∀ terms : Finset (Finset (Fin n)),
      (∀ T ∈ terms, T.card ≤ w) →
        ε < error (bias n) (andFunction n) (evalDNF terms) := by
  have hεmass : ε < Real.exp (-1) := by simpa [Real.exp_neg, one_div] using hε
  have hεgap : ε < 1 - Real.exp (-1) := by linarith [exp_neg_one_le_half]
  have hmass := mass_tendsto_exp_neg_one.eventually (eventually_gt_nhds hεmass)
  have hgap := ((fixed_power_tendsto_one w).sub mass_tendsto_exp_neg_one).eventually
    (eventually_gt_nhds hεgap)
  filter_upwards [eventually_ge_atTop 2, hmass, hgap] with n hn hm hg
  intro terms hw
  rcases Finset.eq_empty_or_nonempty terms with hterms | hterms
  · subst terms
    rw [andFunction, empty_dnf_error, Fintype.card_fin]
    exact hm
  · apply lt_of_lt_of_le hg
    simpa only [andFunction, Fintype.card_fin] using
      nonempty_dnf_error_ge (bias_pos hn).le (bias_lt_one hn).le terms hterms w hw

/-- A quantified counterexample to a high-bias, dimension-free width bound
under bounded resampling influence alone. -/
theorem bounded_influence_obstruction (w : ℕ) {ε : ℝ} (hε0 : 0 < ε)
    (hε : ε < 1 / Real.exp 1) :
    ∃ n : ℕ, 2 ≤ n ∧ 0 < bias n ∧ bias n < 1 ∧ Monotone (andFunction n) ∧
      totalInfluence (bias n) (andFunction n) ≤ 2 ∧
      ∀ terms : Finset (Finset (Fin n)), (∀ T ∈ terms, T.card ≤ w) →
        ε < error (bias n) (andFunction n) (evalDNF terms) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_every_dnf_error_gt w hε0 hε)
  let n := max N 2
  have hn : 2 ≤ n := le_max_right _ _
  exact ⟨n, hn, bias_pos hn, bias_lt_one hn, andAll_monotone,
    andFunction_totalInfluence_le_two hn, hN n (le_max_left _ _)⟩

end NarrowDNF.HighBiasObstruction
