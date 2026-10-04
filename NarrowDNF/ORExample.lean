import NarrowDNF.HighBiasObstruction
import NarrowDNF.Junta

/-!
# The original low-bias OR example

The sequence is exactly `p_n = 1/n`. Its resampling influence stays bounded,
but every junta on a fixed number of coordinates has uniformly positive
approximation error as the dimension tends to infinity.
-/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace NarrowDNF.ORExample
open ProductMeasure Influence
attribute [local instance] Classical.propDecidable

section FiniteCube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def orAll (x : Cube ι) : Bool := decide (∃ i, x i = true)

omit [DecidableEq ι] in
@[simp] theorem orAll_eq_true (x : Cube ι) : orAll x = true ↔ ∃ i, x i = true := by
  simp [orAll]

omit [DecidableEq ι] in
@[simp] theorem orAll_eq_false (x : Cube ι) : orAll x = false ↔ ∀ i, x i = false := by
  simp [orAll, Bool.not_eq_true]

omit [DecidableEq ι] in
theorem orAll_monotone : Monotone (orAll : Cube ι → Bool) := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨i, hi⟩ := (orAll_eq_true x).mp hx
  exact (orAll_eq_true y).mpr ⟨i, Bool.eq_true_of_true_le (by simpa [hi] using hxy i)⟩

theorem probability_all_false (p : ℝ) :
    probability p (fun x : Cube ι => ∀ i, x i = false) = (1-p)^Fintype.card ι := by
  have hp (x : Cube ι) : (∀ i, x i = false) ↔ x = fun _ => false := by
    constructor
    · exact funext
    · intro h; simp [h]
  unfold probability expectation
  simp_rw [hp]
  simp [mul_ite, weight, bitWeight]

theorem orAll_mean (p : ℝ) :
    expectation p (fun x : Cube ι => boolValue (orAll x)) = 1 - (1-p)^Fintype.card ι := by
  have hfun : (fun x : Cube ι => boolValue (orAll x)) =
      fun x => (1 : ℝ) - if ∀ i, x i = false then 1 else 0 := by
    funext x
    simp only [← orAll_eq_false]
    cases orAll x <;> simp [boolValue]
  rw [hfun]
  change expectation p (fun x : Cube ι => 1 - if ∀ i, x i = false then 1 else 0) = _
  have hsub : ∀ F G : Cube ι → ℝ,
      expectation p (fun x => F x - G x) = expectation p F - expectation p G := by
    intro F G
    simp [expectation, mul_sub, Finset.sum_sub_distrib]
  rw [hsub, expectation_const]
  exact congrArg (fun t : ℝ => 1-t) (probability_all_false p)

theorem orAll_sensitivity (p : ℝ) :
    expectation p (sensitivity (orAll : Cube ι → Bool)) =
      (Fintype.card ι : ℝ) * (1-p)^(Fintype.card ι - 1) := by
  have h := Russo.monotone_expectation_hasDerivAt p (orAll : Cube ι → Bool) orAll_monotone
  have hfun : (fun q => expectation q (fun x : Cube ι => boolValue (orAll x))) =
      (fun q : ℝ => 1 - (1-q)^Fintype.card ι) := funext orAll_mean
  rw [hfun] at h
  have hd : HasDerivAt (fun q : ℝ => 1 - (1-q)^Fintype.card ι)
      ((Fintype.card ι : ℝ) * (1-p)^(Fintype.card ι - 1)) p := by
    convert (hasDerivAt_const p (1 : ℝ)).sub
      (((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).pow (Fintype.card ι)) using 1
    simp
  exact h.unique hd

theorem orAll_totalInfluence (p : ℝ) :
    totalInfluence p (orAll : Cube ι → Bool) =
      2 * p * (1-p) * (Fintype.card ι : ℝ) * (1-p)^(Fintype.card ι - 1) := by
  rw [totalInfluence_eq_sensitivity, orAll_sensitivity]
  ring

def zeroOn (J : Finset ι) (x : Cube ι) : Prop := ∀ i ∈ J, x i = false

theorem probability_zeroOn (p : ℝ) (J : Finset ι) :
    probability p (zeroOn J) = (1-p)^J.card := by
  calc
    _ = expectation p (fun x : Cube ι =>
        (fun z : J → Bool => if ∀ i, z i = false then (1 : ℝ) else 0) (fun i => x i)) := by
      unfold probability
      congr 1
      funext x
      simp [zeroOn]
    _ = expectation p (fun z : J → Bool => if ∀ i, z i = false then (1 : ℝ) else 0) := by
      have h := expectation_restrict (ι := ι) p (fun i : ι => i ∈ J)
        (fun z : {i // i ∈ J} → Bool => if ∀ i, z i = false then (1 : ℝ) else 0)
      convert h using 1
      congr 1
      exact Subsingleton.elim _ _
    _ = _ := by
      simpa only [probability, Fintype.card_coe] using probability_all_false (ι := J) p

/-- If the junta accepts its all-zero input, the all-zero cube point is an error. -/
theorem junta_error_ge_of_zero_true {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : Cube ι → Bool) (hh : h (fun _ => false) = true) :
    (1-p)^Fintype.card ι ≤ error p orAll h := by
  rw [← probability_all_false]
  unfold error probability
  apply expectation_mono hp0 hp1
  intro x
  by_cases hx : ∀ i, x i = false
  · have hx0 : x = fun _ => false := funext hx
    subst x
    simp [orAll, hh]
  · simp [hx]
    split <;> norm_num

/-- If the junta rejects the zero input, every nonzero point that is zero on
its observed coordinates is an error. -/
theorem junta_error_ge_of_zero_false {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Finset ι) (h : Cube ι → Bool) (hJ : IsJuntaOn J h)
    (hh : h (fun _ => false) = false) :
    (1-p)^J.card - (1-p)^Fintype.card ι ≤ error p orAll h := by
  rw [← probability_zeroOn, ← probability_all_false]
  have hsub : probability p (zeroOn J) - probability p (fun x : Cube ι => ∀ i, x i = false) =
      expectation p (fun x => (if zeroOn J x then (1 : ℝ) else 0) -
        if ∀ i, x i = false then 1 else 0) := by
    simp [probability, expectation, mul_sub, Finset.sum_sub_distrib]
  rw [hsub]
  apply expectation_mono hp0 hp1
  intro x
  by_cases hzero : ∀ i, x i = false
  · have hloc : zeroOn J x := fun i _ => hzero i
    simp [hzero, hloc]
    split <;> norm_num
  · by_cases hloc : zeroOn J x
    · have hhx : h x = false := (hJ x (fun _ => false) hloc).trans hh
      have hor : orAll x = true := Bool.eq_true_of_not_eq_false (by simpa using hzero)
      simp [hloc, hzero, hhx, hor]
    · simp [hloc, hzero]
      split <;> norm_num

/-- Exact finite-dimensional lower bound, uniform over the chosen coordinates
and over all Boolean readouts, with no monotonicity assumption on the junta. -/
theorem junta_error_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (J : Finset ι) (hJk : J.card ≤ k) (h : Cube ι → Bool)
    (hJ : IsJuntaOn J h) :
    min ((1-p)^Fintype.card ι) ((1-p)^k - (1-p)^Fintype.card ι) ≤ error p orAll h := by
  cases hh : h (fun _ => false)
  · apply le_trans (min_le_right _ _)
    apply le_trans _ (junta_error_ge_of_zero_false hp0 hp1 J h hJ hh)
    exact sub_le_sub_right (pow_le_pow_of_le_one (by linarith) (by linarith) hJk) _
  · exact le_trans (min_le_left _ _) (junta_error_ge_of_zero_true hp0 hp1 h hh)

end FiniteCube

/-- The original low-bias parameter, retained without a reparameterization. -/
def bias (n : ℕ) : ℝ := 1 / (n : ℝ)

def orFunction (n : ℕ) : Cube (Fin n) → Bool := orAll

theorem bias_pos {n : ℕ} (hn : 2 ≤ n) : 0 < bias n := by
  exact one_div_pos.mpr (by exact_mod_cast (show 0 < n by omega))

theorem bias_le_half {n : ℕ} (hn : 2 ≤ n) : bias n ≤ 1/2 := by
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)

theorem orFunction_totalInfluence {n : ℕ} (hn : 2 ≤ n) :
    totalInfluence (bias n) (orFunction n) = 2 * (1 - 1 / (n : ℝ))^n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpow : (1-bias n)^n = (1-bias n)^(n-1) * (1-bias n) := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n by omega)]
  have hb : bias n * (n : ℝ) = 1 := by unfold bias; field_simp
  rw [orFunction, orAll_totalInfluence, Fintype.card_fin]
  calc
    _ = 2 * (bias n * (n : ℝ)) * ((1-bias n)^(n-1) * (1-bias n)) := by ring
    _ = _ := by rw [hb, ← hpow]; simp [bias]

theorem orFunction_totalInfluence_le_two {n : ℕ} (hn : 2 ≤ n) :
    totalInfluence (bias n) (orFunction n) ≤ 2 := by
  rw [orFunction_totalInfluence hn]
  change 2 * (1-bias n)^n ≤ 2
  have hp0 := (bias_pos hn).le
  have hp1 : bias n ≤ 1 := le_trans (bias_le_half hn) (by norm_num)
  nlinarith [pow_le_one₀ (show 0 ≤ 1-bias n by linarith)
    (show 1-bias n ≤ 1 by linarith) (n := n)]

/-- The bounded influence converges to the stated nonzero limiting value. -/
theorem orFunction_totalInfluence_tendsto :
    Tendsto (fun n : ℕ => totalInfluence (bias n) (orFunction n))
      atTop (𝓝 (2 / Real.exp 1)) := by
  have h : Tendsto (fun n : ℕ => 2 * (HighBiasObstruction.bias n)^n)
      atTop (𝓝 (2 * Real.exp (-1))) :=
    tendsto_const_nhds.mul HighBiasObstruction.mass_tendsto_exp_neg_one
  have h' : Tendsto (fun n : ℕ => totalInfluence (bias n) (orFunction n))
      atTop (𝓝 (2 * Real.exp (-1))) := h.congr' (by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (orFunction_totalInfluence hn).symm)
  simpa [Real.exp_neg, div_eq_mul_inv] using h'

/-- Every fixed-size junta stays a constant distance away, uniformly over
both its coordinate set and its arbitrary Boolean readout. -/
theorem eventually_every_junta_error_gt (k : ℕ) {ε : ℝ} (_hε0 : 0 < ε)
    (hε : ε < 1 / Real.exp 1) :
    ∀ᶠ n : ℕ in atTop, ∀ J : Finset (Fin n), J.card ≤ k →
      ∀ h : Cube (Fin n) → Bool, IsJuntaOn J h →
        ε < error (bias n) (orFunction n) h := by
  have hεmass : ε < Real.exp (-1) := by simpa [Real.exp_neg, one_div] using hε
  have hεgap : ε < 1 - Real.exp (-1) := by
    linarith [HighBiasObstruction.exp_neg_one_le_half]
  have hmass := HighBiasObstruction.mass_tendsto_exp_neg_one.eventually
    (eventually_gt_nhds hεmass)
  have hgap := ((HighBiasObstruction.fixed_power_tendsto_one k).sub
    HighBiasObstruction.mass_tendsto_exp_neg_one).eventually (eventually_gt_nhds hεgap)
  filter_upwards [eventually_ge_atTop 2, hmass, hgap] with n hn hm hg
  intro J hJk h hJ
  have hlower := junta_error_ge (bias_pos hn).le
    (le_trans (bias_le_half hn) (by norm_num : (1 : ℝ)/2 ≤ 1)) k J hJk h hJ
  apply lt_of_lt_of_le _ hlower
  apply lt_min
  · simpa [bias, HighBiasObstruction.bias] using hm
  · simpa [bias, HighBiasObstruction.bias] using hg

/-- An explicit dimension-independent positive error threshold works for every
fixed junta size, while the exact original OR sequence has influence at most 2. -/
theorem bounded_influence_junta_obstruction :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 ≤ n ∧ 0 < bias n ∧ bias n ≤ 1/2 ∧ Monotone (orFunction n) ∧
      totalInfluence (bias n) (orFunction n) ≤ 2 ∧
      ∀ J : Finset (Fin n), J.card ≤ k → ∀ h : Cube (Fin n) → Bool,
        IsJuntaOn J h → δ < error (bias n) (orFunction n) h := by
  let δ : ℝ := (1 / Real.exp 1) / 2
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ : δ < 1 / Real.exp 1 := by
    have he : 0 < 1 / Real.exp 1 := by positivity
    dsimp [δ]; linarith
  refine ⟨δ, hδ0, fun k => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_every_junta_error_gt k hδ0 hδ)
  refine ⟨max N 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  exact ⟨hn2, bias_pos hn2, bias_le_half hn2, orAll_monotone,
    orFunction_totalInfluence_le_two hn2, hN n (le_trans (le_max_left _ _) hn)⟩

end NarrowDNF.ORExample
