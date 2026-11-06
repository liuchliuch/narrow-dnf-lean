#!/usr/bin/env python3
"""Exercise the pinned official Comparator with isolated expected failures.

Called by compare.sh after the real paper comparison, with the absolute path
to its already checked Comparator binary. The inherited PATH must contain its
matching lean4export and the same Landrun adapter used for the real comparison.
All Lean fixtures and build products stay in .lake/comparator-negative/;
neither the proof library nor the production challenge is changed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parent.parent
SCRATCH = ROOT / ".lake/comparator-negative"
LOGS = ROOT / ".lake/verification"
NAMESPACE = "NarrowDNFComparatorControl"
TARGET = f"{NAMESPACE}.target"
WHITELIST = {"propext", "Quot.sound", "Classical.choice"}
SUCCESS = "Your solution is okay!"
KERNEL_SUCCESS = "Lean default kernel accepts the solution"


def source(body: str) -> str:
    return f"namespace {NAMESPACE}\n{body}\nend {NAMESPACE}\n"


TRUE_PROOF = source("theorem target : True := True.intro")
DEFINITION_PROOF = source(
    "def token : Nat := 0\n"
    "theorem target : token = token := rfl"
)

# The exact diagnostics below come from the pinned upstream revision:
# Comparator/Compare.lean:53,83 and Comparator/Axioms.lean:45.
CASES = (
    (
        "positive",
        "Positive",
        DEFINITION_PROOF,
        DEFINITION_PROOF,
        None,
    ),
    (
        "type",
        "Type",
        TRUE_PROOF,
        source("theorem target : False → False := fun h => h"),
        f"Challenge and solution theorem statement do not match: '{TARGET}'",
    ),
    (
        "definition",
        "Definition",
        DEFINITION_PROOF,
        source("def token : Nat := 1\ntheorem target : token = token := rfl"),
        "Const does not match between challenge and target "
        f"'{NAMESPACE}.token'",
    ),
    (
        "axiom",
        "Axiom",
        TRUE_PROOF,
        source(
            "axiom forbiddenWitness : True\n"
            "theorem target : True := forbiddenWitness"
        ),
        f"Illegal axiom detected: '{NAMESPACE}.forbiddenWitness'",
    ),
)


def prepare() -> dict:
    """Create a dependency-free project using the production trust settings."""
    production = json.loads((ROOT / "Verification/config.json").read_text())
    axioms = production.get("permitted_axioms", [])
    if len(axioms) != 3 or set(axioms) != WHITELIST:
        raise ValueError("production Comparator axiom whitelist has changed")
    if production.get("enable_nanoda") is not False:
        raise ValueError("production Comparator kernel configuration has changed")
    if production.get("definition_names"):
        raise ValueError("production Comparator unexpectedly permits definition holes")

    (SCRATCH / "Controls").mkdir(parents=True, exist_ok=True)
    (SCRATCH / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
    (SCRATCH / "lakefile.toml").write_text(
        'name = "comparator_negative"\n'
        'version = "0.1.0"\n\n'
        '[[lean_lib]]\nname = "Controls"\nglobs = ["Controls.*"]\n'
    )
    # Supply the empty manifest before the sandbox runs: it permits writes to
    # .lake/, while no package download or project-root manifest write is needed.
    (SCRATCH / "lake-manifest.json").write_text(json.dumps({
        "version": "1.1.0",
        "packagesDir": ".lake/packages",
        "packages": [],
        "name": "comparator_negative",
        "lakeDir": ".lake",
    }, indent=2) + "\n")

    for slug, stem, challenge, solution, _ in CASES:
        (SCRATCH / f"Controls/{stem}Challenge.lean").write_text(challenge)
        (SCRATCH / f"Controls/{stem}Solution.lean").write_text(solution)
        config = {
            "challenge_module": f"Controls.{stem}Challenge",
            "solution_module": f"Controls.{stem}Solution",
            "theorem_names": [TARGET],
            "permitted_axioms": axioms,
            "enable_nanoda": production["enable_nanoda"],
        }
        (SCRATCH / f"{slug}.json").write_text(json.dumps(config, indent=2) + "\n")
    return production


def run_case(binary: Path, slug: str, expected: str | None) -> dict:
    command = ["lake", "env", str(binary), f"{slug}.json"]
    env = os.environ.copy()
    # Construct a fresh Lean search path for this dependency-free project even
    # when the caller is inside the production project's `lake env`.
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    env.setdefault("LEAN_NUM_THREADS", "1")
    failure = None
    returncode = None
    try:
        result = subprocess.run(
            command, cwd=SCRATCH, env=env, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, encoding="utf-8",
            errors="replace", timeout=300, check=False,
        )
        output = result.stdout
        returncode = result.returncode
    except subprocess.TimeoutExpired as exc:
        raw = exc.stdout or b""
        output = raw.decode("utf-8", errors="replace") if isinstance(raw, bytes) else raw
        failure = "Comparator control exceeded the 300 second timeout"
    except OSError as exc:
        output = ""
        failure = f"Could not start Comparator control: {exc}"

    log = LOGS / f"negative-{slug}.log"
    log.write_text(
        "Command: " + json.dumps(command) + "\n"
        + f"Working directory: {SCRATCH}\n"
        + f"Expected diagnostic: {expected or KERNEL_SUCCESS}\n\n"
        + output
        + (f"\nRUNNER ERROR: {failure}\n" if failure else "")
    )
    if expected is None:
        passed = failure is None and returncode == 0 and all(
            marker in output for marker in (KERNEL_SUCCESS, SUCCESS)
        )
    else:
        # An unrelated compiler, sandbox, exporter or configuration failure is
        # not evidence that Comparator rejected the intended mutation.
        passed = (
            failure is None and returncode is not None and returncode > 0
            and expected in output and SUCCESS not in output
        )
    return {
        "case": slug,
        "status": "PASS" if passed else "FAIL",
        "expected": expected or "successful statement comparison and kernel replay",
        "returncode": returncode,
        "runner_error": failure,
        "log": str(log.relative_to(ROOT)),
        "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("comparator", type=Path, help="absolute pinned Comparator binary path")
    args = parser.parse_args()
    binary = args.comparator
    if not binary.is_absolute() or not binary.is_file() or not os.access(binary, os.X_OK):
        parser.error("comparator must be an existing executable at an absolute path")

    LOGS.mkdir(parents=True, exist_ok=True)
    report = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "status": "FAIL",
        "comparator": str(binary),
        "scope": "isolated Comparator controls; no paper proof fixtures",
        "cases": [],
    }
    try:
        production = prepare()
        report["permitted_axioms"] = production["permitted_axioms"]
        report["enable_nanoda"] = production["enable_nanoda"]
        for slug, _, _, _, expected in CASES:
            result = run_case(binary, slug, expected)
            report["cases"].append(result)
            print(f"{result['status']}: Comparator {slug} control ({result['log']})", flush=True)
            if result["status"] != "PASS":
                # In particular, a failed positive control prevents reporting
                # any subsequent negative control as meaningful evidence.
                break
        if len(report["cases"]) == len(CASES) and all(
            item["status"] == "PASS" for item in report["cases"]
        ):
            report["status"] = "PASS"
    except (OSError, ValueError) as exc:
        report["setup_error"] = str(exc)
        print(f"FAIL: Comparator control setup: {exc}", file=sys.stderr)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    summary = LOGS / "negative-summary.json"
    summary.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{report['status']}: Comparator control summary ({summary.relative_to(ROOT)})")
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
