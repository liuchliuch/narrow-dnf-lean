#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/environment.sh

python3 scripts/check_paper.py
python3 scripts/check_project.py
python3 scripts/check_dependencies.py
lake build NarrowDNF
lake env lean --trust=0 scripts/Audit.lean
python3 scripts/semantic_checks.py
