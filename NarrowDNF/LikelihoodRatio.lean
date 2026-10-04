import NarrowDNF.LoadTransport
import NarrowDNF.MinimalElements
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp

namespace NarrowDNF.ProductMeasure
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit Bernoulli point mass in terms of the input's Hamming weight. -/
theorem weight_eq_hamming (p : ℝ) (x : Cube ι) :
    weight p x = p^(support x).card * (1-p)^(Fintype.card ι-(support x).card) := by
  classical
  have hf : Finset.univ.filter (fun i => ¬ x i = true) = (support x)ᶜ := by
    ext i
    simp [support]
  unfold weight bitWeight
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [hf, Finset.card_compl]
  rfl

/-- Exact likelihood-ratio identity used in Lemma 3.3, with division justified
by full support. -/
theorem forcing_likelihood_ratio {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : Cube ι) :
    weight (2*p-p^2) x / weight p x =
      (2-p)^(support x).card * (1-p)^(Fintype.card ι-(support x).card) := by
  have hp : p ≠ 0 := hp0.ne'
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp1).ne'
  have h1 : (2*p-p^2)/p = 2-p := by field_simp
  have h0 : (1-(2*p-p^2))/(1-p) = 1-p := by field_simp; ring
  rw [weight_eq_hamming, weight_eq_hamming, ← div_mul_div_comm, ← div_pow, ← div_pow, h1, h0]

omit [DecidableEq ι] in
theorem forcing_likelihood_ratio_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (x : Cube ι) {d : ℕ} (hd : Fintype.card ι ≤ d) :
    weight (2*p-p^2) x / weight p x ≤ (2-p)^d := by
  apply (div_le_iff₀ (weight_pos hp0 hp1 x)).mpr
  apply (weight_forcing_le hp0.le hp1.le x).trans
  apply mul_le_mul_of_nonneg_right _ (weight_nonneg hp0.le hp1.le x)
  exact pow_le_pow_right₀ (by linarith) hd

end NarrowDNF.ProductMeasure
