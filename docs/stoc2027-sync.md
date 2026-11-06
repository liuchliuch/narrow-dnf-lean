# STOC source synchronization — November 6, 2026

This revision targets the complete authors' manuscript exported from Overleaf
at `2026-11-06T14:23:17.798488+00:00`, not a newly downloaded arXiv version.
The bundled [source](../paper/Low-Influence-Monotone-Boolean-Functions-STOC-revised.tex)
has SHA-256 `831b1e41f1de90dcc5a7bc75740cd072e1639efba81231607fd09d551c62869e`.
[The manifest](../paper/manifest.json) records its 44,250-byte size, the source
archive hash, the locally compiled PDF hash, and every numbered-result label.
The TeX is preserved byte for byte, including authorship and the AI methodology
statement. The PDF was compiled from that exact source with TeX Live 2024;
all 13 rendered pages were inspected, and the final LaTeX log has no warnings,
undefined references, or overfull/underfull boxes.

## Reviewed mathematical delta

The initial local checkout was clean at `dec03993281f4577eacd4d01a7d52751bb228175`.
A fresh fetch confirmed the same `origin/main` before editing. The comparison
baseline was the preserved arXiv v1 source, whose SHA-256 matches the historical
release record (`b7e89e1b5cfe7c290c88863bd695aea49c848f7c056c33c055fa325f32c7fd75`).
The complete 1,071-line target, including Appendix A, was reviewed against the
baseline. A separate independent review checked the public propositions and
the Comparator model against the revised statements. This manuscript
is a complete article with one appendix; it contains no separate embedded
second full-paper version.

The three headline results retain all definitions, hypotheses, conclusions,
constants and quantifier order. Conjecture 1.1, Theorem 1.2, Lemma 2.1, and the
shift/closure/load-transport lemma bodies are identical after whitespace
normalization; the [statement comparison record](../Verification/stoc2027-20261106/source-comparison.json)
contains the baseline and target hashes. The controlled-monotonicization and certificate statements only
change equation presentation. Their existing unconditional proofs remain the
public implementations. The complete numbered mapping and moved atom-recovery
proof are described in [paper correspondence](paper-correspondence.md).

Two focused proof updates make the new exposition explicit in Lean:

- The high-bias argument at source lines 819–834 now directly bounds bit-flip
  influence by `c / p < 2 * c`. `CompactNormalization.lean` proves
  `totalFlipInfluence_le_of_relativeBoundary` and
  `highBias_totalFlipInfluence_lt`. `AllBiasReduction.lean` uses this bound,
  with `totalInfluence_le_half_totalFlipInfluence` providing the proved
  conversion to the existing compact-junta interface. No premise is added.
- Remark 3.3 at source lines 601–602 distinguishes the general decoder
  obstruction from Hatami's uniform-bias construction. `HatamiActivation.lean`
  proves `localMass_half`, `thresholdActivation_half_constant`, and
  `paperActivation_half_constant`, including the actual activation family.

`Activation.force_refines` already proves the newly expanded explanation at
source lines 501–504. The R/Q atom-recovery argument has moved from Appendix B
into Lemma 3.2; its formal proof did not require alteration. The existing
correction to Hatami's auxiliary Fourier-coefficient inequality remains fully
proved and documented; the target parameters and headline conclusions are
unchanged. No new mathematical error was found in the reviewed target.

## Verification for this revision

Incremental direct Lean 4.24.0 checks passed for the two normalization/reduction
modules and the complete edited Hatami activation module. They used one worker
and the existing pinned dependency caches.

Fresh local verification passed:

| Check | Result |
| --- | --- |
| All 54 proof modules, built in dependency order with one worker | PASS |
| Complete `lake build NarrowDNF` | PASS, 3,173 build jobs |
| `lean --trust=0 scripts/Audit.lean` | PASS, 1,172 project declarations across 54 modules |
| Transitive axiom whitelist | Only `propext`, `Classical.choice`, `Quot.sound` |
| Exact finite regressions in dimensions 1–3 | PASS |
| Official Comparator for the three independent headline specifications | PASS |
| Official Comparator's Lean kernel replay of the exported solution | PASS |

The finite checks include all 116,640 local increasing activation families in
dimension three and 46,080 exact shift-error inequalities there. These remain
supplementary finite checks, not substitutes for the arbitrary-dimension proofs.

[Local results and input hashes](../Verification/stoc2027-20261106/local-results.json)
identify the checked source files and link the retained build, audit, regression
and production-Comparator logs. The local comparator uses the explicit
unsandboxed macOS adapter; no external nanoda kernel was used.

The isolated Comparator controls run a positive case and require exact rejection
diagnostics for changed theorem types, changed referenced definitions, and a
forbidden axiom. An initial local fixture failed before comparison because its
hyphenated Lake manifest name was not encoded as a Lean name; the fixture now
uses the valid identifier `comparator_negative`. This setup failure is not
counted as a successful negative control.

The [Lean verification workflow](https://github.com/liuchliuch/narrow-dnf-lean/actions/workflows/lean.yml)
runs the full pipeline, including all four controls, with real Landrun on Linux.
Its commit-associated run and retained job logs provide the hosted evidence.
The local record above claims only its listed completed checks; it does not
infer a hosted result or reuse older release acceptance logs.

## Local environment recovery

An initial incremental `lake env lean` call encountered macOS system Git's
Xcode-license failure. Lake interpreted the failed remote lookup as a changed
mathlib URL and removed the shared mathlib checkout before its clone failed.
No `lake update` or intentional dependency clean was issued. All Lake calls
were stopped. Under the shared cross-task file lock, the missing directory was
restored from a clean local copy at exactly the pinned mathlib commit, including
its pre-existing compiled cache; no dependency was rebuilt or upgraded.

This checkout then switched to its own APFS copies of the pinned dependency
caches. Subsequent checks use those isolated copies. `environment.sh` selects
the installed Command Line Tools for this process on macOS and requires a
successful Git invocation before Lake; `check_dependencies.py` verifies every
pinned dependency commit and remote URL before either verification script can
start Lake. These changes prevent the observed failed-Git reconciliation path
without changing system configuration. All heavy local verification is run
under the requested shared `fcntl.flock`, held until subprocess completion.
