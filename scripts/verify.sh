#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/check_project.py
lake build NarrowDNF
lake env lean --trust=0 scripts/Audit.lean
python3 scripts/semantic_checks.py
