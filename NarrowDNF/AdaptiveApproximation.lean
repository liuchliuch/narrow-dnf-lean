import NarrowDNF.ControlledMonotonicization
import NarrowDNF.PaperCertificates
import NarrowDNF.MainStatements
import Mathlib.Algebra.Order.Floor.Ring

/-! Quantitative reduction from an actual adaptive representation to a narrow
DNF. The actual existence input is supplied separately by `HatamiInput.lean`. -/
noncomputable section
namespace NarrowDNF
open ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The shift-certificate part of Theorem 1.2 with all actual structural inputs
exposed. `HatamiInput.lean` supplies the proved existence of these inputs. -/
theorem adaptive_approximation_to_dnf {p ε L : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hε : 0 < ε) (hL0 : 0 ≤ L) {d : ℕ} {f h : Cube ι → Bool}
    (hf : Monotone f) {J : Activation ι} (hJ : J.Increasing)
    (hd : J.ArityLE d) (hh : J.Measurable h)
    (he : error p f h ≤ ε/4) (hL : J.load p ≤ L) :
    ∃ terms : Finset (Finset ι),
      (∀ T ∈ terms, T.card ≤ Nat.ceil (4 * (2 : ℝ)^d * L / ε)) ∧
      error p f (evalDNF terms) ≤ ε := by
  classical
  have ha : (0 : ℝ) < ε/4 := by positivity
  obtain ⟨D, u, hu, hm, heu, hcost⟩ :=
    Activation.controlled_monotonicization hp0 hp1 ha.le hL0 hf hJ hd hh he hL (ε/4) ha
  let w := Nat.ceil (4 * (2 : ℝ)^d * L / ε)
  let terms := (J.force D).truncatedTerms u w
  refine ⟨terms, ?_, ?_⟩
  · exact fun T hT => Activation.truncatedTerms_width _ u w hT
  · have hcost' : expectation p (fun x => (((J.force D).activeFinset x).card : ℝ)) ≤
        2 * (2 : ℝ)^d * L := by
      have ha0 : ε/4 ≠ 0 := ne_of_gt ha
      rw [div_self ha0] at hcost
      have hp : (2-p)^d ≤ (2:ℝ)^d := pow_le_pow_left₀ (by linarith) (by linarith) d
      have hnon : (0:ℝ) ≤ L*2 := mul_nonneg hL0 (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hp hnon]
    have hbound := (Activation.certificates_and_truncation
      (Activation.force_increasing hJ D) hu hm p hp0.le hp1.le w).2.2.2.2
    have hceil : 4 * (2 : ℝ)^d * L / ε ≤ (w : ℝ) := Nat.le_ceil _
    have hbudget : 2 * (2 : ℝ)^d * L / (w+1 : ℝ) ≤ ε/2 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ) < (w:ℝ)+1)).mpr
      have hmul := (div_le_iff₀ hε).mp hceil
      nlinarith
    have heug : error p u ((J.force D).truncatedDNF u w) ≤ ε/2 :=
      hbound.1.trans (hbound.2.trans ((div_le_div_of_nonneg_right hcost' (by positivity)).trans hbudget))
    have htriangle := error_triangle hp0.le hp1.le f u ((J.force D).truncatedDNF u w)
    change error p f ((J.force D).truncatedDNF u w) ≤ ε
    linarith

end NarrowDNF
