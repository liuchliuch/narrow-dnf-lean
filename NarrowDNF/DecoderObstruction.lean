import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.NormNum
import NarrowDNF.AdaptiveShift

/-!
# The same-partition obstruction in Appendix B.1

Points are the three bits `(b,a₁,a₂)`. The only activation is the full indexing
set, activated exactly when `b=true`. Its adaptive atom therefore is the empty
atom when `b=false`, and an atom recording the entire point when `b=true`.
`Option Point` is an injective encoding of precisely these atoms.

All probabilities are exact rationals under the uniform measure: each point
has mass 1/8. The finite checks below use Lean's kernel-reduced `decide`, not
`native_decide`, an oracle, or an imported proposition.
-/

namespace NarrowDNF.DecoderObstruction

abbrev Point := Bool × Bool × Bool

def atom (x : Point) : Option Point := if x.1 then some x else none

def Measurable (v : Point → Bool) : Prop :=
  ∀ x y, atom x = atom y → v x = v y

instance (v : Point → Bool) : Decidable (Measurable v) :=
  inferInstanceAs (Decidable (∀ x y : Point, atom x = atom y → v x = v y))

def target (x : Point) : Bool := x.2.1 || x.2.2

def decoder (x : Point) : Bool := if x.1 then target x else true

def lowerShift (v : Point → Bool) (x : Point) : Bool := v x && v (true, x.2)

def uniformError (v : Point → Bool) : ℚ :=
  ∑ x : Point, if target x = v x then 0 else 1 / 8

/-- The literal activation family specified in the paper. -/
def activation : Activation (Fin 3) where
  fires S x := S = Finset.univ ∧ x 0 = true
  locality S x y hxy := by
    constructor
    · rintro ⟨rfl, hx⟩
      exact ⟨rfl, (hxy 0 (Finset.mem_univ 0)).symm.trans hx⟩
    · rintro ⟨rfl, hy⟩
      exact ⟨rfl, (hxy 0 (Finset.mem_univ 0)).trans hy⟩

theorem activation_increasing : activation.Increasing := by
  intro S x y hxy hx
  refine ⟨hx.1, ?_⟩
  have h := hxy 0
  rw [hx.2] at h
  cases hy : y 0
  · rw [hy] at h
    exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) h)
  · rfl

theorem mem_active_iff (x : Cube (Fin 3)) (i : Fin 3) :
    i ∈ activation.active x ↔ x 0 = true := by
  constructor
  · rintro ⟨S, _, hS⟩
    exact hS.2
  · intro hx
    exact ⟨Finset.univ, Finset.mem_univ i, rfl, hx⟩

theorem sameAtom_iff (x y : Cube (Fin 3)) :
    activation.SameAtom x y ↔ (x 0 = false ∧ y 0 = false) ∨ x = y := by
  constructor
  · intro hxy
    by_cases hx : x 0 = true
    · right
      funext i
      exact hxy.2 i ((mem_active_iff x i).mpr hx)
    · left
      refine ⟨Bool.eq_false_iff.mpr hx, Bool.eq_false_iff.mpr ?_⟩
      intro hy
      have hi := (mem_active_iff y 0).mpr hy
      rw [← hxy.1] at hi
      exact hx ((mem_active_iff x 0).mp hi)
  · rintro (⟨hx, hy⟩ | rfl)
    · constructor
      · ext i
        simp [mem_active_iff, hx, hy]
      · intro i hi
        have := (mem_active_iff x i).mp hi
        simp [hx] at this
    · exact ⟨rfl, fun _ _ => rfl⟩

def toCube (x : Point) : Cube (Fin 3) :=
  fun i => if i = 0 then x.1 else if i = 1 then x.2.1 else x.2.2

theorem toCube_injective : Function.Injective toCube := by
  intro x y hxy
  have h0 := congrFun hxy 0
  have h1 := congrFun hxy 1
  have h2 := congrFun hxy 2
  apply Prod.ext
  · simpa [toCube] using h0
  · apply Prod.ext
    · simpa [toCube] using h1
    · simpa [toCube] using h2

/-- The finite atom encoding used in every exhaustive theorem below is exactly
the shared adaptive-atom relation for the paper's single activation. -/
theorem atom_matches_activation (x y : Point) :
    activation.SameAtom (toCube x) (toCube y) ↔ atom x = atom y := by
  rw [sameAtom_iff]
  have heq : toCube x = toCube y ↔ x = y :=
    ⟨fun h => toCube_injective h, congrArg toCube⟩
  rw [heq]
  rcases x with ⟨b, a₁, a₂⟩
  rcases y with ⟨c, d₁, d₂⟩
  cases b <;> cases c <;> simp [toCube, atom]

theorem target_monotone : Monotone target := by decide

theorem decoder_measurable : Measurable decoder := by decide

theorem decoder_error : uniformError decoder = 1 / 8 := by
  norm_num [uniformError, Fintype.sum_prod_type, Fintype.sum_bool, target, decoder]

theorem lowerShift_decoder : lowerShift decoder = target := by decide

theorem target_not_measurable : ¬ Measurable target := by decide

theorem constant_one_error : uniformError (fun _ => true) = 1 / 4 := by
  norm_num [uniformError, Fintype.sum_prod_type, Fintype.sum_bool, target]

theorem constant_one_monotone : Monotone (fun _ : Point => true) := by decide

theorem constant_one_measurable : Measurable (fun _ : Point => true) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The Bayes decoder's error is globally optimal on the original partition. -/
theorem every_decoder_error (v : Point → Bool) (hv : Measurable v) :
    (1 / 8 : ℚ) ≤ uniformError v := by
  have h : ∀ v : Point → Bool, Measurable v → (1 / 8 : ℚ) ≤ uniformError v := by decide +kernel
  exact h v hv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every increasing decoder on the same adaptive partition has error at
least 1/4, strictly above the Bayes decoder's 1/8. -/
theorem every_increasing_decoder_error (v : Point → Bool)
    (hv : Measurable v) (hm : Monotone v) : (1 / 4 : ℚ) ≤ uniformError v := by
  have h : ∀ v : Point → Bool, Measurable v → Monotone v →
      (1 / 4 : ℚ) ≤ uniformError v := by decide +kernel
  exact h v hv hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- If the empty atom is labeled zero, its three accepted target points alone
already contribute 3/8 error, as stated in Appendix B.1. -/
theorem empty_atom_zero_error (v : Point → Bool) (hv : Measurable v)
    (hz : v (false, false, false) = false) : (3 / 8 : ℚ) ≤ uniformError v := by
  have h : ∀ v : Point → Bool, Measurable v → v (false, false, false) = false →
      (3 / 8 : ℚ) ≤ uniformError v := by decide +kernel
  exact h v hv hz

end NarrowDNF.DecoderObstruction
