# Verification

## Build and proof audit

The repository uses Lean 4.24.0 and mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Install
[elan](https://github.com/leanprover/elan) and run:

```sh
source scripts/environment.sh && lake exe cache get
scripts/verify.sh
```

Python 3 and Bash are required. The current target source is identified by
[`paper/manifest.json`](../paper/manifest.json); revision-specific results are
recorded separately in the [STOC synchronization report](stoc2027-sync.md).
The script:

1. Checks the bundled paper artifacts against their manifest, then checks that
   every proof module is imported by `NarrowDNF.lean`, rejects proof
   placeholders and added axioms, and checks challenge isolation.
2. Builds all 54 proof modules.
3. Audits the transitive axiom closure of every project-origin declaration,
   including private and generated declarations, regardless of namespace.
4. Replays imported modules with `lean --trust=0` and checks the closed headline
   theorem types.
5. Runs exact rational finite regressions through dimension three. These are
   supplementary tests, not proofs for arbitrary dimension.

For a clean project rebuild, run
`source scripts/environment.sh && lake clean narrow-dnf` before the script.
Dependency caches are reused; these commands do not rebuild all of mathlib
from source. To inspect an individual proof, open its `.lean` file in a
Lean-enabled editor.

Both verification scripts check Git availability and verify all nine dependency
commits and remote URLs before invoking Lake. On macOS the environment helper
selects installed Command Line Tools for the current process. If dependency
caches are shared through writable symlinks, first prepare an isolated local
copy; Lake can reconcile package URLs even during `lake env`. The current
revision used isolated cache copies after the recovery documented in the
synchronization report. No dependency pin was changed.

## Independent statement comparison

`Verification/Model.lean` imports only mathlib and restates the cube,
Bernoulli product weights, resampling influence, local activation family,
adaptive atoms, DNF semantics and minimal accepted points. It contains no
paper theorem proofs. Its definitions use the same names as the proof library,
but are compiled in a separate environment.

`Verification/Challenge.lean` explicitly states Theorem 1.2, Lemma 2.1 and
Conjecture 1.1 of the November 6, 2026 STOC source snapshot. The complete
review found these statements unchanged from arXiv v1. Its three intentional
`sorry` placeholders specify the challenge;
they are never imported by `NarrowDNF` or `Verification/Solution.lean`.
`Solution.lean` repeats the statements and applies the actual unconditional
proofs. The comparator checks statement and referenced-definition identity,
rejects unapproved transitive axioms, and replays the exported solution with
Lean's kernel. There are no definition holes. A successful comparison verifies
these explicit propositions and their referenced definitions; it does not
establish correspondence with an informal source that has not been reviewed.

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
axiom and kernel checks, but provides **no process sandbox**. Local macOS
verification uses this mode. `enable_nanoda` is false, so this configuration
does not invoke an independent external kernel such as nanoda. GitHub Actions
is configured to use real landrun on Linux;
local verification does not establish that a future hosted CI run passed.

## Negative controls and CI evidence

The comparison workflow also runs intentional negative controls in a separate,
ignored scratch project. They use the same pinned Comparator and axiom
whitelist as the real challenge, and test three distinct failures:

- A changed theorem type, even though both fixture statements have proofs.
- A changed referenced definition with an otherwise identical theorem type.
- A proof with an unapproved transitive axiom.

Each control must fail for its expected reason. A setup failure or unrelated
compilation error does not count as a successful negative control. These
fixtures never enter the proof library or the production challenge.

GitHub Actions runs the proof verification and Comparator with the pinned
Linux Landrun sandbox and retains their logs. The workflow run page associates
each result and job log with the corresponding pushed commit. Local logs, hosted CI results,
and historical release checks are separate evidence and should be read as such.

## Trust and mathematical scope

The proof whitelist is exactly `propext`, `Classical.choice` and `Quot.sound`.
Source scanning and finite tests complement the kernel; neither replaces it.
Comparator verifies agreement with the reviewed challenge, not the correctness
of the translation from informal mathematics. Review the challenge, its model,
and [paper correspondence](paper-correspondence.md) to assess that translation.
The supporting numbered statements are checked by the full library build and
axiom audit; comparator targets the three headline results.

The Linux launcher inserts a command boundary before invoking the pinned real
Landrun binary. This preserves lean4export's own `--` delimiter with Landrun's
CLI parser. All sandbox permissions and the mathematical statement interfaces
are unchanged. Local development mode remains explicitly unsandboxed.
