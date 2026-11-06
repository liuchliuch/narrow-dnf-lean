#!/usr/bin/env python3
"""Read-only preflight: refuse implicit reconciliation of pinned dependencies."""
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
manifest = json.loads((root / 'lake-manifest.json').read_text())
failures = []
for package in manifest['packages']:
    path = root / manifest['packagesDir'] / package['name']
    try:
        def git(*args):
            return subprocess.check_output(
                ['git', '-C', str(path), *args], text=True, stderr=subprocess.PIPE).strip()
        head = git('rev-parse', 'HEAD')
        url = git('remote', 'get-url', 'origin')
        if head != package['rev'] or url != package['url']:
            failures.append(f"{package['name']}: checkout differs from pinned commit or URL")
    except subprocess.CalledProcessError as error:
        failures.append(f"{package['name']}: Git preflight failed: {error.stderr.strip()}")
if failures:
    print('\n'.join(failures), file=sys.stderr)
    sys.exit('Refusing to invoke Lake on missing or mismatched dependencies. '
             'Prepare the pinned cache in an isolated checkout first.')
print(f"PASS: {len(manifest['packages'])} pinned dependency commits and URLs")
