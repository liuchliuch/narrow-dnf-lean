import NarrowDNF.ProductMeasure
import NarrowDNF.UniformHypercontractivity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A conservative biased two-point hypercontractive estimate

This is a genuine fourth-moment contraction for arbitrary real endpoint values.
The deliberately conservative noise parameter is sufficient for compact-bias
uniform junta approximation. Tensorization and finite duality then yield actual
arbitrary-dimensional biased hypercontractivity. The junta conclusion is proved
in BiasedFriedgut.
-/

namespace NarrowDNF.BiasedHypercontractivity

/-- Bernoulli mean of two real endpoint values. -/
def bitMean (p a b : ℝ) : ℝ := (1-p)*a+p*b

/-- Apply the scalar noise operator to the lower endpoint. -/
def noiseZero (p ρ a b : ℝ) : ℝ := bitMean p a b + ρ*(a-bitMean p a b)

/-- Apply the scalar noise operator to the upper endpoint. -/
def noiseOne (p ρ a b : ℝ) : ℝ := bitMean p a b + ρ*(b-bitMean p a b)

/-- Explicit sum-of-nonnegative-terms identity behind the two-point estimate. -/
theorem fourth_gap_identity (p ρ m d : ℝ) :
    (m^2+p*(1-p)*d^2)^2 -
        ((1-p)*(m-ρ*p*d)^4+p*(m+ρ*(1-p)*d)^4) =
      (2-8*ρ^2)*m^2*(p*(1-p))*d^2 +
        (p*(1-p))*(p*(1-p)-3*ρ^4)*d^4 +
        9*ρ^4*(p*(1-p))^2*d^4 +
        2*((1-p)*(m*ρ*(-p*d)-ρ^2*(-p*d)^2)^2 +
          p*(m*ρ*((1-p)*d)-ρ^2*((1-p)*d)^2)^2) := by ring

/-- A biased two-point `2 → 4` hypercontractive inequality, in integer-power form. -/
theorem fourth_contraction (p ρ a b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hρ2 : ρ^2 ≤ 1/4) (hρ4 : 3*ρ^4 ≤ p*(1-p)) :
    (1-p)*(noiseZero p ρ a b)^4+p*(noiseOne p ρ a b)^4 ≤
      ((1-p)*a^2+p*b^2)^2 := by
  have hpbar : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have ht : 0 ≤ p*(1-p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have htwo : 0 ≤ 2-8*ρ^2 := by linarith
  have hlast : 0 ≤ p*(1-p)-3*ρ^4 := sub_nonneg.mpr hρ4
  have hnonneg : 0 ≤
      (2-8*ρ^2)*(bitMean p a b)^2*(p*(1-p))*(b-a)^2 +
        (p*(1-p))*(p*(1-p)-3*ρ^4)*(b-a)^4 +
        9*ρ^4*(p*(1-p))^2*(b-a)^4 +
        2*((1-p)*((bitMean p a b)*ρ*(-p*(b-a))-ρ^2*(-p*(b-a))^2)^2 +
          p*((bitMean p a b)*ρ*((1-p)*(b-a))-ρ^2*((1-p)*(b-a))^2)^2) := by
    positivity
  rw [← fourth_gap_identity] at hnonneg
  have hmean : (bitMean p a b)^2+p*(1-p)*(b-a)^2 = (1-p)*a^2+p*b^2 := by
    unfold bitMean
    ring
  have hzero : bitMean p a b-ρ*p*(b-a) = noiseZero p ρ a b := by
    unfold noiseZero bitMean
    ring
  have hone : bitMean p a b+ρ*(1-p)*(b-a) = noiseOne p ρ a b := by
    unfold noiseOne bitMean
    ring
  rw [hmean,hzero,hone] at hnonneg
  linarith

/-- A fixed noise parameter works for every bias in `[lam,1-lam]`. -/
theorem fourth_contraction_compact (lam p a b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1/2)
    (hp0 : lam ≤ p) (hp1 : p ≤ 1-lam) :
    (1-p)*(noiseZero p (lam/4) a b)^4+p*(noiseOne p (lam/4) a b)^4 ≤
      ((1-p)*a^2+p*b^2)^2 := by
  apply fourth_contraction p (lam/4) a b (hlam0.trans hp0) (by linarith)
  · nlinarith [sq_nonneg lam]
  · have ht : lam^2 ≤ p*(1-p) := by
      have := mul_le_mul hp0 (show lam ≤ 1-p by linarith) hlam0 (by linarith : 0 ≤ p)
      nlinarith
    have hlamsq : lam^2 ≤ 1 := by nlinarith
    have h4 : lam^4 ≤ lam^2 := by nlinarith [sq_nonneg (lam^2), mul_nonneg (sq_nonneg lam) (sub_nonneg.mpr hlamsq)]
    nlinarith [sq_nonneg lam]

/-- One-bit biased noise on a function, ready for finite tensorization. -/
def bitNoise (p ρ : ℝ) (f : Bool → ℝ) (b : Bool) : ℝ :=
  bitMean p (f false) (f true) + ρ*(f b-bitMean p (f false) (f true))

/-- The scalar contraction in the finite-weight operator API. -/
theorem bitNoise_contract24 (p ρ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hρ2 : ρ^2 ≤ 1/4) (hρ4 : 3*ρ^4 ≤ p*(1-p)) (f : Bool → ℝ) :
    (∑ b : Bool, ProductMeasure.bitWeight p b * (bitNoise p ρ f b)^4) ≤
      (∑ b : Bool, ProductMeasure.bitWeight p b * (f b)^2)^2 := by
  simpa [bitNoise, noiseZero, noiseOne, ProductMeasure.bitWeight, add_comm] using
    fourth_contraction p ρ (f false) (f true) hp0 hp1 hρ2 hρ4

/-- Compact-bias-uniform contraction in the finite-weight operator API. -/
theorem bitNoise_contract24_compact (lam p : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1/2)
    (hp0 : lam ≤ p) (hp1 : p ≤ 1-lam) (f : Bool → ℝ) :
    (∑ b : Bool, ProductMeasure.bitWeight p b * (bitNoise p (lam/4) f b)^4) ≤
      (∑ b : Bool, ProductMeasure.bitWeight p b * (f b)^2)^2 := by
  simpa [bitNoise, noiseZero, noiseOne, ProductMeasure.bitWeight, add_comm] using
    fourth_contraction_compact lam p (f false) (f true) hlam0 hlam1 hp0 hp1

/-- The normalized Fourier kernel is the elementary biased averaging operator. -/
theorem standardKernelOperator_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ) :
    Hypercontractivity.kernelOperator (ProductMeasure.bitWeight p)
      (Hypercontractivity.standardKernel p ρ) = bitNoise p ρ := by
  have hkernel (a b : Bool) : ProductMeasure.bitWeight p b *
      (1+ρ*Fourier.standardBit p a*Fourier.standardBit p b) =
        (1-ρ)*ProductMeasure.bitWeight p b + ρ*(if a=b then 1 else 0) := by
    have h := Fourier.bit_kernel hp0 hp1 a b
    simp only [Fourier.bitBasis, Bool.false_eq_true, if_false, if_true, one_mul] at h
    calc
      _ = (1-ρ)*ProductMeasure.bitWeight p b + ρ*(ProductMeasure.bitWeight p b *
          (1+Fourier.standardBit p a*Fourier.standardBit p b)) := by ring
      _ = _ := by rw [h]
  funext f a
  unfold Hypercontractivity.kernelOperator Hypercontractivity.standardKernel
  simp_rw [hkernel]
  cases a <;> simp [bitNoise, bitMean, ProductMeasure.bitWeight] <;> ring

/-- Genuine biased kernel L2-to-L4 contraction on a compact interval of biases. -/
theorem biased_kernel_contract24 (lam p : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1/2)
    (hp0 : lam ≤ p) (hp1 : p ≤ 1-lam) :
    Hypercontractivity.Contract24 (ProductMeasure.bitWeight p)
      (Hypercontractivity.kernelOperator (ProductMeasure.bitWeight p)
        (Hypercontractivity.standardKernel p (lam/4))) := by
  rw [standardKernelOperator_eq (hlam0.trans_le hp0) (by linarith : p < 1)]
  exact fun f => bitNoise_contract24_compact lam p hlam0.le hlam1 hp0 hp1 f

/-- Arbitrary-dimensional compact-bias-uniform L2-to-L4 hypercontractivity
for the actual Fourier-defined noise operator. -/
theorem biased_spectral_contract24 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam p : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1/2)
    (hp0 : lam ≤ p) (hp1 : p ≤ 1-lam) (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p
      (fun x => BourgainNoise.tensorNoise p (fun _ => lam/4) f x ^ 4) ≤
        (ProductMeasure.expectation p (fun x => f x ^ 2))^2 := by
  have hpnonneg : 0 ≤ p := hlam0.le.trans hp0
  have hple : p ≤ 1 := by linarith
  have h := Hypercontractivity.contract24_product (ProductMeasure.bitWeight p)
    (ProductMeasure.bitWeight_nonneg hpnonneg hple)
    (Hypercontractivity.standardKernel p (lam/4))
    (biased_kernel_contract24 lam p hlam0 hlam1 hp0 hp1) ι f
  simp only [Hypercontractivity.productOperator_standardKernel, Hypercontractivity.productWeight] at h
  unfold ProductMeasure.expectation ProductMeasure.weight
  convert h using 1
  · congr 1
    ext x
    simp
  · congr 2
    ext x
    simp

/-- Dual compact-bias L(4/3)-to-L2 hypercontractivity in polynomial moment form. -/
theorem biased_spectral_contract43 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam p : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1/2)
    (hp0 : lam ≤ p) (hp1 : p ≤ 1-lam) (f : (ι → Bool) → ℝ) :
    (ProductMeasure.expectation p
      (fun x => BourgainNoise.tensorNoise p (fun _ => lam/4) f x ^ 2))^2 ≤
        (BourgainDuality.moment43 (ProductMeasure.weight p) f)^3 := by
  apply BourgainDuality.dual_contract24
    (ProductMeasure.weight p)
    (ProductMeasure.weight_nonneg (hlam0.le.trans hp0) (by linarith))
    (BourgainNoise.tensorNoise p (fun _ => lam/4))
  · intro g h
    simpa only [ProductMeasure.expectation, mul_assoc] using
      BourgainNoise.tensorNoise_selfAdjoint p (fun _ => lam/4) g h
  · exact fun g => biased_spectral_contract24 lam p hlam0 hlam1 hp0 hp1 g

end NarrowDNF.BiasedHypercontractivity
