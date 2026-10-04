import Mathlib.Data.Real.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Independently reviewable statement model

This module imports only mathlib. It restates the finite probability model and
definitions used in the paper statements, without importing NarrowDNF proofs.
The names deliberately match the proof library: comparator checks their types
and bodies across the two separate environments. Keep this file under review;
do not regenerate it automatically from the solution.
-/

noncomputable section
open scoped BigOperators
namespace NarrowDNF

abbrev Cube (ι : Type*) := ι → Bool

structure Activation (ι : Type*) where
  fires : Finset ι → Cube ι → Prop
  locality : ∀ S x y, (∀ i ∈ S, x i = y i) → (fires S x ↔ fires S y)

namespace ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p
def weight (p : ℝ) (x : ι → Bool) : ℝ := ∏ i, bitWeight p (x i)
def expectation (p : ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  ∑ x, weight p x * F x
def probability (p : ℝ) (P : (ι → Bool) → Prop) [DecidablePred P] : ℝ :=
  expectation p (fun x => if P x then 1 else 0)
def error (p : ℝ) (f g : (ι → Bool) → Bool) : ℝ :=
  probability p (fun x => f x ≠ g x)
end ProductMeasure

namespace FiberShift
def mismatch (a b : Bool) : ℝ := if a = b then 0 else 1
end FiberShift

namespace Influence
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def resamplingInfluence (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ :=
  ProductMeasure.expectation p (fun x =>
    (1-p) * FiberShift.mismatch (f x) (f (Function.update x i false)) +
      p * FiberShift.mismatch (f x) (f (Function.update x i true)))
def totalInfluence (p : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  ∑ i, resamplingInfluence p f i
def sensitivity (f : (ι → Bool) → Bool) (x : ι → Bool) : ℝ :=
  ∑ i, FiberShift.mismatch (f x) (f (Function.update x i (!(x i))))
end Influence

section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def TermHolds (T : Finset ι) (x : Cube ι) : Prop := ∀ i ∈ T, x i = true
def DNFHolds (terms : Finset (Finset ι)) (x : Cube ι) : Prop :=
  ∃ T ∈ terms, TermHolds T x
def support (x : Cube ι) : Finset ι := Finset.univ.filter fun i => x i = true
def MinimalAccepted (f : Cube ι → Prop) (x : Cube ι) : Prop :=
  f x ∧ ∀ y, y ≤ x → f y → y = x

namespace Activation
def Increasing (J : Activation ι) : Prop := ∀ S, Monotone (J.fires S)
def active (J : Activation ι) (x : Cube ι) : Set ι :=
  {i | ∃ S, i ∈ S ∧ J.fires S x}
def SameAtom (J : Activation ι) (x y : Cube ι) : Prop :=
  J.active x = J.active y ∧ ∀ i ∈ J.active x, x i = y i
def Measurable (J : Activation ι) (u : Cube ι → Bool) : Prop :=
  ∀ x y, J.SameAtom x y → u x = u y
def ArityLE (J : Activation ι) (d : ℕ) : Prop :=
  ∀ S, d < S.card → ∀ x, ¬ J.fires S x
noncomputable def load (J : Activation ι) (p : ℝ) : ℝ := by
  classical exact ∑ S : Finset ι, (S.card : ℝ) * ProductMeasure.probability p (J.fires S)
end Activation
end Cube

attribute [local instance] Classical.propDecidable
def evalDNF {ι : Type*} (terms : Finset (Finset ι)) (x : Cube ι) : Bool :=
  decide (DNFHolds terms x)

end NarrowDNF
