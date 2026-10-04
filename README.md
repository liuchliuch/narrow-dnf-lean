# Narrow DNF approximation in Lean

Lean 4 formalization of **Bounded Relative Boundary Implies Narrow DNF
Approximation**, by Chenghua Liu and Boning Meng
([arXiv:2609.00240v1](https://arxiv.org/abs/2609.00240v1)).

The main result approximates an increasing Boolean function of bounded total
resampling influence, for `0 < p ≤ 1/2`, by a monotone DNF of width at most
`exp(C (K + 1)² / ε²)`. The formal proof supplies `C = 10¹³`. A separate
argument proves Friedgut's all-bias conjecture under bounded relative boundary.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The toolchain is Lean **4.24.0**. Mathlib and its dependencies are pinned in
`lakefile.toml` and `lake-manifest.json`.

## Main declarations

Import `NarrowDNF.Paper` for the headline theorems, or `NarrowDNF` for the
complete library, including the paper's examples and obstructions.

| Paper result | Lean declaration |
| --- | --- |
| Theorem 1.2 | `NarrowDNF.main_narrow_dnf` |
| Lemma 2.1 | `NarrowDNF.hatami_arity_load` |
| Conjecture 1.1, proved | `NarrowDNF.friedgut_all_bias` |

The theorem propositions are in
[`MainStatements.lean`](NarrowDNF/MainStatements.lean); their unconditional
proofs are in [`Paper.lean`](NarrowDNF/Paper.lean). The Hatami, Bourgain and
compact-bias junta ingredients are proved in this repository.
See [paper correspondence](docs/paper-correspondence.md) for the remaining
numbered results, definitions and proof architecture.

## Verification

```sh
scripts/verify.sh
scripts/compare.sh
```

The first command builds every proof module, audits transitive axioms, replays
imports with Lean's trust level zero, and runs exact finite regression checks.
The second runs the official [Lean comparator](https://github.com/leanprover/comparator)
on the three headline results. Its challenge has an independent, mathlib-only
definition model; its solution imports the actual proofs. The three intentional
challenge placeholders are excluded from the proof library. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted in proofs.

See [verification instructions](docs/verification.md) for the comparator setup,
the explicit unsandboxed macOS mode, and the limits of each check. GitHub
Actions is configured to run the build and verification on Linux.

## Source correction

The formalization repairs an auxiliary Fourier-coefficient bound in the cited
Hatami proof, retaining the target paper's activation parameters and conclusions.
The counterexample and corrected cross-term estimates are proved in Lean and
explained in [paper correspondence](docs/paper-correspondence.md#auxiliary-source-correction).

## License and citation

Released under the [Apache License 2.0](LICENSE). Please cite the paper when
using this formalization; bibliographic metadata is in [CITATION.cff](CITATION.cff).
