# Verification

## Build and proof audit

The repository uses Lean 4.24.0 and mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Install
[elan](https://github.com/leanprover/elan) and run:

```sh
lake exe cache get
scripts/verify.sh
```

Python 3 and Bash are required. The script:

1. Checks that every proof module is imported by `NarrowDNF.lean`, rejects proof
   placeholders and added axioms, and checks challenge isolation.
2. Builds all 54 proof modules.
3. Audits the transitive axiom closure of every project-origin declaration,
   including private and generated declarations, regardless of namespace.
4. Replays imported modules with `lean --trust=0` and checks the closed headline
   theorem types.
5. Runs exact rational finite regressions through dimension three. These are
   supplementary tests, not proofs for arbitrary dimension.

For a clean project rebuild, run `lake clean narrow-dnf` before the script.
Dependency caches are reused; these commands do not rebuild all of mathlib
from source. To inspect an individual proof, open its `.lean` file in a
Lean-enabled editor.

## Independent statement comparison

`Verification/Model.lean` imports only mathlib and restates the cube,
Bernoulli product weights, resampling influence, local activation family,
adaptive atoms, DNF semantics and minimal accepted points. It contains no
paper theorem proofs. Its definitions use the same names as the proof library,
but are compiled in a separate environment.

`Verification/Challenge.lean` explicitly states Theorem 1.2, Lemma 2.1 and
Conjecture 1.1. Its three intentional `sorry` placeholders specify the challenge;
they are never imported by `NarrowDNF` or `Verification/Solution.lean`.
`Solution.lean` repeats the statements and applies the actual unconditional
proofs. The comparator checks statement and referenced-definition identity,
rejects unapproved transitive axioms, and replays the exported solution with
Lean's kernel. There are no definition holes.

On Linux, install [landrun](https://github.com/Zouuup/landrun) and run:

```sh
scripts/compare.sh
```

The script installs comparator and its matching exporter under the ignored
`.lake/comparator-tools/` directory. Comparator is pinned to commit
`97ef939c9fe3f8abf93e4adb654517476da7a66f`, the upstream Lean 4.24.0 branch;
its own manifest pins lean4checker and lean4export. An existing checkout can be
supplied through `COMPARATOR_HOME`, but must match that revision.

For macOS or another development environment without landrun:

```sh
scripts/compare.sh --unsandboxed
```

This explicit mode uses a local process adapter. It performs the same statement,
axiom and kernel checks, but provides **no process sandbox**. The release's
local comparator run used this mode. No independent external kernel such as
nanoda was used. GitHub Actions is configured to use real landrun on Linux;
local verification does not establish that a future hosted CI run passed.

## Trust and mathematical scope

The proof whitelist is exactly `propext`, `Classical.choice` and `Quot.sound`.
Source scanning and finite tests complement the kernel; neither replaces it.
Comparator verifies agreement with the reviewed challenge, not the correctness
of the translation from informal mathematics. Review the challenge, its model,
and [paper correspondence](paper-correspondence.md) to assess that translation.
The supporting numbered statements are checked by the full library build and
axiom audit; comparator targets the three headline results.
