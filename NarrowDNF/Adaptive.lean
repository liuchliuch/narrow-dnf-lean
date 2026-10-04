import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Monotone.Basic

/-! Local activation families and their adaptive atoms. The global-input encoding
of a local activation carries an explicit locality proof, so it does not grant
an activation access to coordinates outside its indexing set. -/
namespace NarrowDNF

abbrev Cube (ι : Type*) := ι → Bool

structure Activation (ι : Type*) where
  fires : Finset ι → Cube ι → Prop
  locality : ∀ S x y, (∀ i ∈ S, x i = y i) → (fires S x ↔ fires S y)

namespace Activation
variable {ι : Type*} [DecidableEq ι]

def Increasing (J : Activation ι) : Prop := ∀ S, Monotone (J.fires S)

def active (J : Activation ι) (x : Cube ι) : Set ι :=
  {i | ∃ S, i ∈ S ∧ J.fires S x}

def SameAtom (J : Activation ι) (x y : Cube ι) : Prop :=
  J.active x = J.active y ∧ ∀ i ∈ J.active x, x i = y i

def Measurable (J : Activation ι) (u : Cube ι → Bool) : Prop :=
  ∀ x y, J.SameAtom x y → u x = u y

omit [DecidableEq ι] in
theorem active_mono {J : Activation ι} (hJ : J.Increasing) : Monotone J.active := by
  intro x y hxy i hi
  obtain ⟨S, hiS, hS⟩ := hi
  exact ⟨S, hiS, hJ S hxy hS⟩

omit [DecidableEq ι] in
theorem mem_active_of_fires {J : Activation ι} {S : Finset ι} {x : Cube ι}
    (h : J.fires S x) {i : ι} (hi : i ∈ S) : i ∈ J.active x := ⟨S, hi, h⟩

noncomputable def zeroOutside (J : Activation ι) (x : Cube ι) : Cube ι :=
  by classical exact fun i => if i ∈ J.active x then x i else false

omit [DecidableEq ι] in
theorem zeroOutside_le (J : Activation ι) (x : Cube ι) : J.zeroOutside x ≤ x := by
  classical
  intro i
  simp only [zeroOutside]
  split <;> simp_all

omit [DecidableEq ι] in
theorem zeroOutside_sameAtom {J : Activation ι} (hJ : J.Increasing) (x : Cube ι) :
    J.SameAtom x (J.zeroOutside x) := by
  classical
  have hf : ∀ S, J.fires S x ↔ J.fires S (J.zeroOutside x) := by
    intro S
    constructor
    · intro hS
      apply (J.locality S x (J.zeroOutside x) ?_).mp hS
      intro i hi
      simp [zeroOutside, mem_active_of_fires hS hi]
    · exact hJ S (J.zeroOutside_le x)
  constructor
  · ext i
    simp only [active, Set.mem_setOf_eq]
    exact exists_congr fun S => and_congr_right fun _ => hf S
  · intro i hi
    simp [zeroOutside, hi]

omit [DecidableEq ι] in
/-- The exact positive certificate in Lemma 4.1: the positive labels in the
active union force acceptance at every larger extension. -/
theorem positive_certificate {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u)
    {x : Cube ι} (hx : u x = true) {y : Cube ι}
    (hy : ∀ i ∈ J.active x, x i = true → y i = true) : u y = true := by
  classical
  have hzero : u (J.zeroOutside x) = true :=
    (hm x (J.zeroOutside x) (zeroOutside_sameAtom hJ x)).symm.trans hx
  have hle : J.zeroOutside x ≤ y := by
    intro i
    by_cases hi : i ∈ J.active x
    · by_cases hxi : x i = true
      · simp [zeroOutside, hi, hxi, hy i hi hxi]
      · have hfalse : x i = false := Bool.eq_false_iff.mpr hxi
        simp [zeroOutside, hi, hfalse]
    · simp [zeroOutside, hi]
  have := hu hle
  cases huy : u y
  · rw [hzero, huy] at this
    exact False.elim ((by decide : ¬(true ≤ false)) this)
  · rfl

end Activation
end NarrowDNF
