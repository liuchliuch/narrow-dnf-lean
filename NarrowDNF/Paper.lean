import NarrowDNF.MainReduction
import NarrowDNF.HatamiInput
import NarrowDNF.BiasedFriedgut
import NarrowDNF.AllBiasReduction

/-!
# Unconditional headline results of Liu–Meng, arXiv:2609.00240v1

Every external input used by these wrappers is proved in this project. The
Wrappers take no Hatami, Bourgain, junta, or approximation assumption.
The proposition definitions expose the paper's complete quantifier order.
-/
namespace NarrowDNF

/-- Lemma 2.1: simultaneous approximation, increasing activation family,
arity, and multiplicity-counted load with the paper's exact parameters. -/
theorem hatami_arity_load : HatamiArityLoad := HatamiInput.hatami_arity_load

/-- Theorem 1.2: dimension- and low-bias-uniform narrow monotone DNF
approximation, with a proved explicit absolute constant. -/
theorem main_narrow_dnf : NarrowDNFApproximation := narrowDNF_of_hatami hatami_arity_load

/-- Conjecture 1.1, proved: all-bias increasing-family approximation by a family
whose minimal elements have uniformly bounded Hamming weight. -/
theorem friedgut_all_bias : FriedgutAllBias :=
  friedgutAllBias_of_lowBias_and_compactJunta main_narrow_dnf
    BiasedFriedgut.compactBiasMonotoneJunta

end NarrowDNF
