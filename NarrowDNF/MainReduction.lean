import NarrowDNF.AdaptiveApproximation
import NarrowDNF.WidthBound
import Mathlib.Tactic.GCongr

/-! The modular low-bias implication. The actual proved `HatamiArityLoad` input
is supplied by `Paper.lean`, giving the unconditional headline theorem. -/
noncomputable section
namespace NarrowDNF

/-- Complete low-bias main-theorem assembly from the exact, separately stated
Hatami existence proposition. The proposition is not postulated as an axiom. -/
theorem narrowDNF_of_hatami (hHatami : HatamiArityLoad) : NarrowDNFApproximation := by
  refine ⟨WidthBound.absoluteConstant, WidthBound.absoluteConstant_pos, ?_⟩
  intro n hn K p ε hK hp0 hpHalf hε hε1 f hf hI
  have hp1 : p < 1 := by linarith
  have ha : 0 < ε/4 := by positivity
  have ha1 : ε/4 ≤ 1 := by linarith
  obtain ⟨J, h, hJ, herr, hm, harity, hload⟩ := hHatami n p hp0 hpHalf f (ε/4) ha ha1
  have hc : Nat.ceil (Influence.totalInfluence p f) ≤ Nat.ceil K := Nat.ceil_mono hI
  have hcr : (Nat.ceil (Influence.totalInfluence p f) : ℝ) ≤ (Nat.ceil K : ℝ) := by
    exact_mod_cast hc
  have hd : Nat.ceil (1000 * (Nat.ceil (Influence.totalInfluence p f) : ℝ) / (ε/4)) ≤
      WidthBound.degree K ε := by
    apply Nat.ceil_mono
    change 1000 * (Nat.ceil (Influence.totalInfluence p f) : ℝ) / (ε/4) ≤
      4000 * (Nat.ceil K : ℝ) / ε
    calc
      _ = 4000 * (Nat.ceil (Influence.totalInfluence p f) : ℝ) / ε := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcr (by norm_num)) hε.le
  have hdJ : J.ArityLE (WidthBound.degree K ε) := by
    intro S hS x
    exact harity S (hd.trans_lt hS) x
  have hloadJ : J.load p ≤ WidthBound.loadBound K ε := by
    apply hload.trans
    apply Real.exp_le_exp.mpr
    change 10000000000 * (Nat.ceil (Influence.totalInfluence p f) : ℝ)^2 / (ε/4)^2 ≤
      160000000000 * (Nat.ceil K : ℝ)^2 / ε^2
    calc
      _ = 160000000000 * (Nat.ceil (Influence.totalInfluence p f) : ℝ)^2 / ε^2 := by ring
      _ ≤ _ := by gcongr
  have hL0 : 0 ≤ WidthBound.loadBound K ε := (Real.exp_pos _).le
  obtain ⟨terms, hw, he⟩ := adaptive_approximation_to_dnf hp0 hp1 hε hL0 hf hJ hdJ hm herr hloadJ
  refine ⟨terms, ?_, he⟩
  intro T hT
  have ht : (T.card : ℝ) ≤ (WidthBound.width K ε : ℝ) := by
    have htNat : T.card ≤ WidthBound.width K ε := by
      simpa only [WidthBound.width] using hw T hT
    exact_mod_cast htNat
  exact ht.trans (WidthBound.width_le_exponential hK hε hε1)

end NarrowDNF
