import NarrowDNF.ConditionalExpectation

/-! Finite product independence and conditional independence of overlapping
local observables. These lemmas justify the overlap-fiber step in Hatami's proof. -/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ConditionalExpectation
open ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fubini over any partition of the coordinate set. -/
theorem expectation_merge (p : ℝ) (P : ι → Prop) [DecidablePred P] (F : Cube ι → ℝ) :
    expectation p F = expectation p (fun z => expectation p (fun y => F (merge P z y))) := by
  let e := Equiv.piEquivPiSubtypeProd P (fun _ : ι => Bool)
  have h := Fintype.sum_equiv e (fun x => weight p x * F x)
    (fun t : ({i // P i} → Bool) × ({i // ¬ P i} → Bool) =>
      weight p t.1 * (weight p t.2 * F (merge P t.1 t.2))) (fun x => by
        have hx : merge P (fun i => x i) (fun i => x i) = x := by
          funext i
          simp [merge]
        change weight p x * F x = weight p (fun i : {i // P i} => x i) *
          (weight p (fun i : {i // ¬ P i} => x i) *
            F (merge P (fun i => x i) (fun i => x i)))
        rw [hx, weight_partition p P x]
        ring)
  unfold expectation
  rw [h, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]

/-- Independence for observables reading complementary coordinate sets. -/
theorem expectation_mul_of_complement_local (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F G : Cube ι → ℝ)
    (hF : ∀ x y, (∀ i, P i → x i = y i) → F x = F y)
    (hG : ∀ x y, (∀ i, ¬ P i → x i = y i) → G x = G y) :
    expectation p (fun x => F x * G x) = expectation p F * expectation p G := by
  have hFm (z : {i // P i} → Bool) (y : {i // ¬ P i} → Bool) :
      F (merge P z y) = F (extendFalse P z) := by
    apply hF
    intro i hi
    simp [merge, extendFalse, hi]
  have hGm (z : {i // P i} → Bool) (y : {i // ¬ P i} → Bool) :
      G (merge P z y) = G (extendFalse (fun i => ¬ P i) y) := by
    apply hG
    intro i hi
    simp [merge, extendFalse, hi]
  rw [expectation_merge p P]
  simp_rw [hFm, hGm, expectation_const_mul]
  rw [expectation_mul_const, ← expectation_local p P F hF,
    ← expectation_local p (fun i => ¬ P i) G hG]

/-- Two local functions become independent after conditioning on the coordinates
in the intersection of their supports. -/
theorem local_conditional_independence {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (S R : Finset ι) (F G : Cube ι → ℝ)
    (hF : ∀ x y, (∀ i ∈ S, x i = y i) → F x = F y)
    (hG : ∀ x y, (∀ i ∈ R, x i = y i) → G x = G y) :
    expectation p (fun x => F x * G x) =
      expectation p (fun x =>
        conditional (fun x : Cube ι => fun i : {i // i ∈ S ∩ R} => x i) (weight p) F x *
        conditional (fun x : Cube ι => fun i : {i // i ∈ S ∩ R} => x i) (weight p) G x) := by
  let T : ι → Prop := fun i => i ∈ S ∩ R
  have hfactor (z : {i // T i} → Bool) :
      expectation p (fun y => F (merge T z y) * G (merge T z y)) =
        expectation p (fun y => F (merge T z y)) *
          expectation p (fun y => G (merge T z y)) := by
    apply expectation_mul_of_complement_local p (fun i : {i // ¬ T i} => i.val ∈ S)
    · intro x y hxy
      apply hF
      intro i hiS
      by_cases hiT : T i
      · simp [merge, hiT]
      · simpa [merge, hiT] using hxy (⟨i,hiT⟩ : {i // ¬ T i}) hiS
    · intro x y hxy
      apply hG
      intro i hiR
      by_cases hiT : T i
      · simp [merge, hiT]
      · have hiS : i ∉ S := by
          intro his
          exact hiT (Finset.mem_inter.mpr ⟨his,hiR⟩)
        simpa [merge, hiT] using hxy (⟨i,hiT⟩ : {i // ¬ T i}) hiS
  rw [expectation_merge p T (fun x => F x * G x)]
  simp_rw [hfactor]
  symm
  change expectation p (fun x : Cube ι => mean (fun x : Cube ι => fun i : {i // T i} => x i)
    (weight p) F (fun i => x i) *
      mean (fun x : Cube ι => fun i : {i // T i} => x i) (weight p) G (fun i => x i)) = _
  trans expectation p (fun x : Cube ι =>
    expectation p (fun y => F (merge T (fun i => x i) y)) *
    expectation p (fun y => G (merge T (fun i => x i) y)))
  · apply congrArg (expectation p)
    funext x
    apply congrArg₂ (fun a b : ℝ => a*b)
    · apply Eq.trans ?_ (mean_restriction (ι := ι) hp0 hp1 T F (fun i => x i))
      exact mean_decidableEq_irrel _ _ _ _ _ _
    · apply Eq.trans ?_ (mean_restriction (ι := ι) hp0 hp1 T G (fun i => x i))
      exact mean_decidableEq_irrel _ _ _ _ _ _
  · exact expectation_restrict p T (fun z => expectation p (fun y => F (merge T z y)) *
      expectation p (fun y => G (merge T z y)))

end NarrowDNF.ConditionalExpectation
