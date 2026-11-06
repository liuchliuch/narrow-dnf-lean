# Correspondence with the paper

Reference: Chenghua Liu and Boning Meng, *Bounded Relative Boundary Implies
Narrow DNF Approximation*, [arXiv:2609.00240](https://arxiv.org/abs/2609.00240).
The current target is the authors' STOC revised manuscript, exported from
[Overleaf](https://www.overleaf.com/project/6ad8d34ce8b959257628193d) at
`2026-11-06T14:23:17.798488+00:00`. The complete source, including Appendix A,
is bundled as [TeX](../paper/Low-Influence-Monotone-Boolean-Functions-STOC-revised.tex)
with a [PDF built from that source](../paper/Low-Influence-Monotone-Boolean-Functions-STOC-revised.pdf).
The source has 44,250 bytes and SHA-256
`831b1e41f1de90dcc5a7bc75740cd072e1639efba81231607fd09d551c62869e`.
[The manifest](../paper/manifest.json) records provenance and artifact hashes.

The previous release targeted [arXiv v1](https://arxiv.org/abs/2609.00240v1),
submitted August 31, 2026 and rechecked on October 4, 2026. These historical
hashes identify the comparison baseline, not the current target or new
verification evidence:

| Historical source | SHA-256 |
| --- | --- |
| arXiv v1 `main.tex` | `b7e89e1b5cfe7c290c88863bd695aea49c848f7c056c33c055fa325f32c7fd75` |
| arXiv v1 PDF | `8bb23d350751f816666ea753a49a11877a9b1f429f8512a0ef08cd49c13b79b3` |

## Changes from arXiv v1

The complete manuscript comparison preserves the definitions, hypotheses,
quantifier order, width bound, Hatami parameters and conclusions of the three
headline results. Changes to typography, exposition, references and the AI
methodology statement are retained in the bundled source. The mathematical
and structural correspondence is:

| arXiv v1 | STOC revised manuscript | Formalization response |
| --- | --- | --- |
| Conjecture 1.1, Theorem 1.2, Lemma 2.1 | Same numbers and statements | Keep the public propositions, unconditional proofs and independent Comparator targets. |
| Lemma 3.2 with atom-recovery proof in Appendix B | Full atom-recovery proof inside Lemma 3.2 | Existing `AdaptiveShift` proofs retain actual input labels and ordered repeated forcing; `Activation.force_refines` proves the explicit refinement observation. |
| Remark B.1 | Remark 3.3, with an explicit distinction between general activations and Hatami's uniform-bias construction | Retain the decoder obstruction; add `HatamiActivation.localMass_half`, `HatamiActivation.thresholdActivation_half_constant` and the paper-family specialization `HatamiActivation.paperActivation_half_constant`. |
| Lemma 3.3 | Lemma 3.4 | Update the load-transport references; the equality and both bounds are unchanged. |
| Theorem 3.4 | Theorem 3.5 | Update the controlled-monotonicization references; the simultaneous error and cost budgets are unchanged. |
| Compact-interval normalization in the all-bias proof | Direct `E_p[sensitivity] ≤ c/p < 2c` for `p > 1/2` | Prove `Influence.totalFlipInfluence_le_of_relativeBoundary` and `Influence.highBias_totalFlipInfluence_lt`; use this bound in `AllBiasReduction`. |
| Remark B.2 | Remark 4.2 | Retain the same high-bias AND sequence and obstruction. |
| Appendix A | Appendix A | Retain the activation construction, parameters and corrected auxiliary Fourier estimates described below. |

See the [synchronization report](stoc2027-sync.md) for revision-specific checks
and their results. Historical acceptance evidence is not used as evidence for
this source snapshot.

## Numbered results

All names below are in the `NarrowDNF` namespace. The first three results have
separate, explicit comparator challenges and an independent definition model.

| Paper | Lean declarations | Source modules |
| --- | --- | --- |
| Conjecture 1.1, proved | `friedgut_all_bias` | `Paper`, `AllBiasReduction`, `BiasedFriedgut` |
| Theorem 1.2 | `main_narrow_dnf` | `Paper`, `MainReduction`, `WidthBound` |
| Lemma 2.1 | `hatami_arity_load` | `Paper`, `HatamiInput`, `HatamiActivation` |
| Lemma 3.1 | `ShiftProbability.one_coordinate_error_le`; `upperShift_coordinateMonotone`; `lowerShift_coordinateMonotone`; `upperShift_preserves_coordinateMonotone`; `lowerShift_preserves_coordinateMonotone` | `FiberShift`, `CoordinateShift`, `ShiftProbability` |
| Lemma 3.2 | `Activation.measurable_upperShift`; `Activation.measurable_lowerShift`; `Activation.measurable_applyShifts` | `AdaptiveShift` |
| Remark 3.3 | `DecoderObstruction.decoder_error`; `lowerShift_decoder`; `target_not_measurable`; `every_increasing_decoder_error`; `empty_atom_zero_error` (all in `DecoderObstruction`); `HatamiActivation.paperActivation_half_constant` | `DecoderObstruction`, `HatamiActivation` |
| Lemma 3.4 | `Activation.load_transport`; `Activation.expected_forced_active_le` | `LoadTransport`, `LikelihoodRatio` |
| Theorem 3.5 | `Activation.controlled_monotonicization` | `ControlledMonotonicization`, `Weighted` |
| Lemma 4.1 | `Activation.certificates_and_truncation` | `Adaptive`, `Certificates`, `CertificateBounds`, `PaperCertificates` |
| Remark 4.2 | `HighBiasObstruction.andFunction_totalInfluence_tendsto`; `andFunction_relativeBoundary_tendsto_atTop`; `eventually_every_dnf_error_gt` (all in `HighBiasObstruction`) | `HighBiasObstruction` |

Additional source claims include the original `p_n = 1/n` OR example
(`ORExample.bounded_influence_junta_obstruction`), the Margulis-Russo derivative
identity (`Russo.totalInfluence_eq_deriv`), the revised direct high-bias
normalization (`Influence.highBias_totalFlipInfluence_lt`), and the equivalence
between bounded minimal elements and positive DNF width (`CanonicalDNF`). The older general
compact-interval normalization `Influence.compact_totalFlipInfluence_le` remains
available as an auxiliary result.

## Definitions and quantifiers

- `Cube (Fin n)` is `Fin n → Bool`, with the coordinatewise order and
  `false < true`. Product probability is an explicit finite sum with point
  weights `∏ i, if x i then p else 1-p`.
- `Influence.totalInfluence` sums disagreement under **independent resampling**
  of each coordinate. A pivotal fiber contributes `2p(1-p)`. Bit-flip
  sensitivity is a separate definition. Their exact relation is proved in
  `Influence.totalInfluence_eq_sensitivity`.
- An `Activation` carries a locality proof for each indexing set. `SameAtom`
  means equal active unions and equal actual input labels on that union.
  `Measurable` means constancy on these finite atoms.
- `Activation.load` sums `|S| Pr[J_S = 1]`, counting overlapping sets with
  multiplicity. `ArityLE d` requires every activation above cardinality `d`
  to vanish. Neither is replaced by a bound on ambient dimension.
- `Activation.force` changes activation tests. It leaves the recorded labels
  as actual input labels. Upper shifts retain the original partition;
  lower shifts use the forced refinement. Iterated closure permits repetitions
  and retains the processing order.
- A DNF is a finite family of positive conjunctions. The empty conjunction
  is true and the empty disjunction is false. Width bounds each term; it
  does not bound the number of terms. `MinimalAccepted` is actual minimality
  in the coordinatewise order.
- In Theorem 1.2, one positive real `C` is chosen before `n`, `K`, `p`, `ε`
  and `f`. The error is additive disagreement. The proof establishes the
  final exponential bound using the explicit constant `10¹³`.
- Lemma 2.1 has no monotonicity assumption on `f`. The same pair `(J,h)`
  satisfies approximation, measurability, increasing activations, arity and
  load. The parameters are exactly `C_f = ceil(I_p(f))`,
  `d = ceil(1000 C_f/a)` and `L = exp(10¹⁰ C_f²/a²)`.
- The all-bias theorem chooses `k` before `p` and `n`. Its hypothesis is
  `p E_p[sensitivity] ≤ c`, as in the paper. The high-bias AND obstruction
  concerns bounded resampling influence alone and does not contradict it.

The shift and load lemmas are also proved at endpoint biases when their
formulas allow this. Lemma 4.1 retains the integer-tail denominator `w+1`,
including `w=0`. The controlled monotonicization proof handles zero load and
selects one realization satisfying both budgets. In the all-bias proof, either
choice at a Bayes threshold tie gives the same error; the formalization uses
the strict half-threshold also used in Appendix A.

## Proof organization

The main chain is:

1. `Fourier`, the hypercontractivity and `Bourgain*` modules prove the analytic
   truncation estimates from finite product probability.
2. `HatamiActivation`, `HatamiResidual`, `HatamiCrossTerms`, `HatamiParameters`
   and `HatamiInput` establish Lemma 2.1 with its source parameters.
3. `ShiftProbability`, `AdaptiveShift`, `LoadTransport` and `Weighted` establish
   controlled monotonicization while preserving exact adaptive measurability.
4. The certificate modules construct a finite positive DNF and bound its
   discarded mass. `MainReduction` and `WidthBound` assemble Theorem 1.2.
5. `BiasedFriedgut` proves the compact-bias monotone junta theorem;
   `ConstantApproximation`, `CompactNormalization`, `Junta` and `AllBiasReduction`
   complete the all-bias conclusion. The direct bit-flip bound is converted to
   the resampling convention of the compact junta interface by
   `Influence.totalInfluence_le_half_totalFlipInfluence`. `Paper.lean` supplies
   unconditional headline wrappers.

## Auxiliary source correction

The cited [Hatami paper](https://doi.org/10.4007/annals.2012.176.1.9),
Annals 176 (2012), p. 517, prints an auxiliary bound
`|f̂(S)| ≤ p^(|S|/2)` for Boolean functions in the stated normalization.
For two-bit XOR at `p = 1/10`, the coefficient is `-9/50`, whose absolute
value exceeds `1/10`. `HatamiCoefficientCounterexample.lean` proves this
normalized counterexample directly.

The proof library instead proves
`|f̂(S)| ≤ (2 sqrt(p(1-p)))^|S|` in `Fourier.lean`, retains the resulting
factors through the cross-term and cardinality-rank estimates, and bounds the
corrected term `2^(9k) δ / ε₁²` in `HatamiParameters.corrected_cross_bound`.
The target paper's `δ = 2^(-100k²)`, `ε₁ = 3^(-10k²) ε₀^(10k)`, arity,
load and final approximation constants are preserved. The formalization does
not rely on the printed false auxiliary inequality.

The source review checked the mathematical definitions, headline quantifiers,
numbered-result statements, dependency assembly, numerical budgets and this
correction against both the original paper and the current STOC source snapshot. Kernel acceptance and comparator
agreement provide the separate mechanical evidence described in
[verification](verification.md); they do not automate the informal-to-formal
translation review.
