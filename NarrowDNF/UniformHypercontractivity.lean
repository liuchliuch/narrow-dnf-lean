import NarrowDNF.Fourier
import NarrowDNF.BourgainNoise
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Finite L2-to-L4 hypercontractivity and its uniform-cube specialization

The moment formulation avoids fractional powers during tensorization.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Hypercontractivity

attribute [local instance] Classical.decEq

variable {α β : Type*} [Fintype α] [Fintype β]

def Contract24 (w : α → ℝ) (T : (α → ℝ) → α → ℝ) : Prop :=
  ∀ f, (∑ x, w x * (T f x)^4) ≤ (∑ x, w x * (f x)^2)^2

/-- Cauchy-Schwarz with arbitrary nonnegative finite weights, applied to
the squared outputs of an L2-to-L4 contraction. -/
theorem cross_moment_le {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    {T : (α → ℝ) → α → ℝ} (hT : Contract24 w T) (f g : α → ℝ) :
    (∑ x, w x * (T f x)^2 * (T g x)^2) ≤
      (∑ x, w x * (f x)^2) * (∑ x, w x * (g x)^2) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (Finset.univ : Finset α)
    (r := fun x => w x * (T f x)^2 * (T g x)^2)
    (f := fun x => w x * (T f x)^4)
    (g := fun x => w x * (T g x)^4)
    (fun x _ => mul_nonneg (hw x) (by positivity))
    (fun x _ => mul_nonneg (hw x) (by positivity))
    (fun x _ => by ring)
  have hf0 : 0 ≤ ∑ x, w x * (f x)^2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)
  have hg0 : 0 ≤ ∑ x, w x * (g x)^2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)
  have hprod := mul_le_mul (hT f) (hT g)
    (Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (by positivity)) (sq_nonneg _)
  have hbound := hcs.trans hprod
  have hnonneg := mul_nonneg hf0 hg0
  nlinarith [sq_nonneg
    ((∑ x, w x * (T f x)^2 * (T g x)^2) -
      (∑ x, w x * (f x)^2) * (∑ x, w x * (g x)^2))]

/-- A weighted sum of squared outputs satisfies the same L2 estimate. This is
the special mixed-norm inequality needed to tensorize L2-to-L4 contractions. -/
theorem vector_moment_le {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    {T : (α → ℝ) → α → ℝ} (hT : Contract24 w T)
    (v : β → ℝ) (hv : ∀ y, 0 ≤ v y) (f : β → α → ℝ) :
    (∑ x, w x * (∑ y, v y * (T (f y) x)^2)^2) ≤
      (∑ y, v y * (∑ x, w x * (f y x)^2))^2 := by
  classical
  have hexpand (F : β → α → ℝ) :
      (∑ x, w x * (∑ y, v y * (F y x)^2)^2) =
        ∑ y, ∑ z, (v y * v z) * (∑ x, w x * (F y x)^2 * (F z x)^2) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hexpand]
  calc
    _ ≤ ∑ y, ∑ z, (v y * v z) *
        ((∑ x, w x * (f y x)^2) * (∑ x, w x * (f z x)^2)) := by
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (cross_moment_le hw hT (f y) (f z))
        (mul_nonneg (hv y) (hv z))
    _ = _ := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

/-- Tensor products preserve the L2-to-L4 contraction property. Both scalar
inequalities are genuine input theorems; no unproved tensorization is assumed. -/
theorem contract24_tensor {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    {v : β → ℝ} (hv : ∀ y, 0 ≤ v y)
    {T : (α → ℝ) → α → ℝ} {U : (β → ℝ) → β → ℝ}
    (hT : Contract24 w T) (hU : Contract24 v U) :
    Contract24 (fun z : α × β => w z.1 * v z.2)
      (fun f z => T (fun a => U (fun b => f (a,b)) z.2) z.1) := by
  intro f
  simp only [Fintype.sum_prod_type]
  have hswap :
      (∑ a, ∑ b, w a * v b * (T (fun a => U (fun b => f (a,b)) b) a)^4) =
        ∑ b, v b * (∑ a, w a * (T (fun a => U (fun b => f (a,b)) b) a)^4) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hswap]
  calc
    _ ≤ ∑ b, v b * (∑ a, w a * (U (fun b => f (a,b)) b)^2)^2 := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hT _) (hv b)
    _ ≤ (∑ a, w a * (∑ b, v b * (f (a,b))^2))^2 :=
      vector_moment_le hv hU w hw (fun a b => f (a,b))
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- One-bit uniform noise in its mean/difference decomposition. -/
def uniformBitNoise (ρ : ℝ) (f : Bool → ℝ) (b : Bool) : ℝ :=
  (f false + f true) / 2 + (if b then ρ else -ρ) * (f true - f false) / 2

/-- The sharp one-bit L2-to-L4 estimate at every |ρ|≤1/sqrt(3), stated
polynomially as 3ρ²≤1. -/
theorem uniform_bit_contract24 (ρ : ℝ) (hρ : 3 * ρ^2 ≤ 1) :
    Contract24 (fun _ : Bool => (1/2 : ℝ)) (uniformBitNoise ρ) := by
  intro f
  have hρ4 : ρ^4 ≤ 1 := by
    nlinarith [sq_nonneg (ρ^2 - 1), sq_nonneg ρ]
  have hcross : (0:ℝ) ≤ ((f false + f true)/2)^2 * ((f true-f false)/2)^2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_right hρ hcross
  have h2 := mul_le_mul_of_nonneg_right hρ4 (by positivity :
    (0:ℝ) ≤ ((f true-f false)/2)^4)
  simp only [Fintype.sum_bool, uniformBitNoise, Bool.false_eq_true, if_false, if_true]
  nlinarith [sq_nonneg (((f true-f false)/2)^2)]

/-- Transport a finite moment inequality across an exact relabeling. -/
theorem contract24_transfer (e : α ≃ β) {w : α → ℝ} {v : β → ℝ}
    {T : (α → ℝ) → α → ℝ} {U : (β → ℝ) → β → ℝ}
    (hw : ∀ a, w a = v (e a))
    (hTU : ∀ f a, T (fun a => f (e a)) a = U f (e a))
    (hT : Contract24 w T) : Contract24 v U := by
  intro f
  have h4 := Fintype.sum_equiv e (fun a => w a * (T (fun a => f (e a)) a)^4)
    (fun b => v b * (U f b)^4) (fun a => by dsimp only; rw [hw, hTU])
  have h2 := Fintype.sum_equiv e (fun a => w a * (f (e a))^2)
    (fun b => v b * (f b)^2) (fun a => by dsimp only; rw [hw])
  rw [← h4, ← h2]
  exact hT _

def productWeight {ι : Type*} [Fintype ι] (w : Bool → ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, w (x i)

def productOperator {ι : Type*} [Fintype ι] (w : Bool → ℝ)
    (K : Bool → Bool → ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ y : ι → Bool, (∏ i, w (y i) * K (x i) (y i)) * f y

def kernelOperator (w : Bool → ℝ) (K : Bool → Bool → ℝ)
    (f : Bool → ℝ) (b : Bool) : ℝ := ∑ c : Bool, w c * K b c * f c

/-- Relabel the coordinate type, preserving all input bits. -/
def cubeEquiv {ι κ : Type*} (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp

theorem productWeight_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : Bool → ℝ) (x : ι → Bool) :
    productWeight w x = productWeight w (cubeEquiv e x) := by
  unfold productWeight
  simpa [cubeEquiv] using e.prod_comp (fun j => w (x (e.symm j)))

theorem productOperator_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : Bool → ℝ) (K : Bool → Bool → ℝ)
    (f : (κ → Bool) → ℝ) (x : ι → Bool) :
    productOperator w K (fun y => f (cubeEquiv e y)) x =
      productOperator w K f (cubeEquiv e x) := by
  unfold productOperator
  apply Fintype.sum_equiv (cubeEquiv e)
  intro y
  congr 1
  simpa [cubeEquiv] using
    e.prod_comp (fun j => w (y (e.symm j)) * K (x (e.symm j)) (y (e.symm j)))

theorem productWeight_option {ι : Type*} [Fintype ι] (w : Bool → ℝ)
    (x : Option ι → Bool) :
    productWeight w x = w (x none) * productWeight w (fun i => x (some i)) := by
  exact Fintype.prod_option (fun i => w (x i))

/-- Split a product-kernel operator into its first coordinate and the rest. -/
theorem productOperator_option {ι : Type*} [Fintype ι] (w : Bool → ℝ)
    (K : Bool → Bool → ℝ) (f : (Option ι → Bool) → ℝ) (x : Option ι → Bool) :
    productOperator w K f x =
      kernelOperator w K (fun b => productOperator w K
        (fun y => f (Equiv.piOptionEquivProd.symm (b,y)))
        (fun i => x (some i))) (x none) := by
  unfold productOperator kernelOperator
  have hsplit := Fintype.sum_equiv (Equiv.piOptionEquivProd (α := ι)
      (β := fun _ => Bool) :
      (Option ι → Bool) ≃ Bool × (ι → Bool))
    (fun y => (∏ i, w (y i) * K (x i) (y i)) * f y)
    (fun z : Bool × (ι → Bool) =>
      w z.1 * K (x none) z.1 *
        (∏ i, w (z.2 i) * K (x (some i)) (z.2 i)) *
        f (Equiv.piOptionEquivProd.symm z)) (fun y => by
          dsimp only
          rw [Fintype.prod_option]
          rw [Equiv.symm_apply_apply]
          rfl)
  trans ∑ z : Bool × (ι → Bool),
      w z.1 * K (x none) z.1 *
        (∏ i, w (z.2 i) * K (x (some i)) (z.2 i)) *
        f (Equiv.piOptionEquivProd.symm z)
  · convert hsplit using 1
    congr 1
    ext y
    simp
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring

/-- Dimension-free tensorization: every scalar two-point L2-to-L4 kernel
inequality extends to arbitrary finite coordinate products. -/
theorem contract24_product (w : Bool → ℝ) (hw : ∀ b, 0 ≤ w b)
    (K : Bool → Bool → ℝ) (hK : Contract24 w (kernelOperator w K))
    (ι : Type*) [Fintype ι] :
    Contract24 (productWeight (ι := ι) w) (productOperator w K) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun ι _ => Contract24 (productWeight (ι := ι) w) (productOperator w K))
    ?_ ?_ ?_ ι
  · intro α β _ e hα
    letI : Fintype α := Fintype.ofEquiv β e.symm
    exact contract24_transfer (cubeEquiv e) (productWeight_equiv e w)
      (productOperator_equiv e w K) hα
  · intro f
    have hconstant (x : PEmpty → Bool) : productOperator w K f x = f x := by
      simp [productOperator]
      exact congrArg f (Subsingleton.elim _ _)
    simp [productWeight, hconstant, ← pow_mul]
  · intro α _ hα
    have hwα : ∀ x : α → Bool, 0 ≤ productWeight w x := by
      intro x
      exact Finset.prod_nonneg fun i _ => hw (x i)
    have h := contract24_transfer
      ((Equiv.piOptionEquivProd (α := α) (β := fun _ => Bool)).symm)
      (w := fun z => w z.1 * productWeight w z.2)
      (v := productWeight (ι := Option α) w)
      (T := fun f z => kernelOperator w K
        (fun b => productOperator w K (fun y => f (b,y)) z.2) z.1)
      (U := productOperator (ι := Option α) w K)
      (by intro z; simp [productWeight_option, Equiv.piOptionEquivProd])
      (by intro f z; rw [productOperator_option]; rfl)
      (contract24_tensor hw hwα hK hα)
    convert h using 1

/-- The normalized Bernoulli spectral-noise kernel. -/
def standardKernel (p ρ : ℝ) (b c : Bool) : ℝ :=
  1 + ρ * Fourier.standardBit p b * Fourier.standardBit p c

theorem standardKernelOperator_half (ρ : ℝ) :
    kernelOperator (ProductMeasure.bitWeight (1/2)) (standardKernel (1/2) ρ) =
      uniformBitNoise ρ := by
  funext f b
  cases b <;>
    norm_num [kernelOperator, Fintype.sum_bool, standardKernel, Fourier.standardBit,
      ProductMeasure.bitWeight, uniformBitNoise] <;> ring

theorem uniform_kernel_contract24 (ρ : ℝ) (hρ : 3 * ρ^2 ≤ 1) :
    Contract24 (ProductMeasure.bitWeight (1/2))
      (kernelOperator (ProductMeasure.bitWeight (1/2)) (standardKernel (1/2) ρ)) := by
  rw [standardKernelOperator_half]
  have hw : ProductMeasure.bitWeight (1/2) = fun _ : Bool => (1/2 : ℝ) := by
    funext b
    cases b <;> norm_num [ProductMeasure.bitWeight]
  rw [hw]
  exact uniform_bit_contract24 ρ hρ

theorem productOperator_standardKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p ρ : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    productOperator (ProductMeasure.bitWeight p) (standardKernel p ρ) f x =
      BourgainNoise.tensorNoise p (fun _ => ρ) f x := by
  convert (BourgainNoise.tensorNoise_eq_productKernel p (fun _ => ρ) f x).symm using 1
  simp only [productOperator, standardKernel]
  congr 1
  ext y
  simp

/-- Arbitrary-dimensional sharp uniform-cube L2-to-L4 hypercontractivity, in
fourth-moment form, for the actual Fourier-defined noise operator. -/
theorem uniform_spectral_contract24 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : 3 * ρ^2 ≤ 1) (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation (1/2)
      (fun x => BourgainNoise.tensorNoise (1/2) (fun _ => ρ) f x ^ 4) ≤
        (ProductMeasure.expectation (1/2) (fun x => f x ^ 2))^2 := by
  have h := contract24_product (ProductMeasure.bitWeight (1/2))
    (ProductMeasure.bitWeight_nonneg (by norm_num) (by norm_num))
    (standardKernel (1/2) ρ) (uniform_kernel_contract24 ρ hρ) ι f
  simp only [productOperator_standardKernel, productWeight] at h
  unfold ProductMeasure.expectation ProductMeasure.weight
  convert h using 1
  · congr 1
    ext x
    simp
  · congr 2
    ext x
    simp

/-- The sharp uniform parameter, written to simplify its exact square. -/
def sharpRho : ℝ := Real.sqrt (1/3)

theorem sharpRho_sq : sharpRho^2 = (1/3 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

theorem sharpRho_pos : 0 < sharpRho := by
  exact Real.sqrt_pos.mpr (by norm_num)

theorem uniform_spectral_sharp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation (1/2)
      (fun x => BourgainNoise.tensorNoise (1/2) (fun _ => sharpRho) f x ^ 4) ≤
        (ProductMeasure.expectation (1/2) (fun x => f x ^ 2))^2 := by
  apply uniform_spectral_contract24
  rw [sharpRho_sq]
  norm_num

/-- The dual L(4/3)-to-L2 Bonami inequality. Squaring the second moment avoids
outer fractional powers while giving the identical sharp inequality. -/
theorem uniform_spectral_contract43 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : 3 * ρ^2 ≤ 1) (f : (ι → Bool) → ℝ) :
    (ProductMeasure.expectation (1/2)
      (fun x => BourgainNoise.tensorNoise (1/2) (fun _ => ρ) f x ^ 2))^2 ≤
        (BourgainDuality.moment43 (ProductMeasure.weight (1/2)) f)^3 := by
  apply BourgainDuality.dual_contract24
    (ProductMeasure.weight (1/2))
    (ProductMeasure.weight_nonneg (by norm_num) (by norm_num))
    (BourgainNoise.tensorNoise (1/2) (fun _ => ρ))
  · intro g h
    simpa only [ProductMeasure.expectation, mul_assoc] using
      BourgainNoise.tensorNoise_selfAdjoint (1/2) (fun _ => ρ) g h
  · exact fun g => uniform_spectral_contract24 ρ hρ g

theorem uniform_spectral_sharp43 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) :
    (ProductMeasure.expectation (1/2)
      (fun x => BourgainNoise.tensorNoise (1/2) (fun _ => sharpRho) f x ^ 2))^2 ≤
        (BourgainDuality.moment43 (ProductMeasure.weight (1/2)) f)^3 := by
  apply uniform_spectral_contract43
  rw [sharpRho_sq]
  norm_num

end NarrowDNF.Hypercontractivity
