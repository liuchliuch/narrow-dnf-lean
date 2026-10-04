#!/usr/bin/env python3
"""Check source coverage and isolation of comparator placeholders.

This lexical preflight complements the kernel and transitive axiom audit.
It does not establish the correctness of mathematical statements or proofs.
"""
from pathlib import Path
import json
import re
import sys

ROOT = Path(__file__).resolve().parent.parent


def code_only(text):
    """Blank nested comments and strings while preserving source locations."""
    out = list(text)
    i = depth = 0
    while i < len(text):
        start = i
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(text))):
            if out[j] != '\n':
                out[j] = ' '
    return ''.join(out)


def imports(text):
    return set(re.findall(r'^import\s+(\S+)\s*$', code_only(text), re.M))


def main():
    sources = sorted((ROOT / 'NarrowDNF').glob('*.lean'))
    aggregate = imports((ROOT / 'NarrowDNF.lean').read_text())
    expected = {'NarrowDNF.' + p.stem for p in sources}
    failures = []
    if aggregate != expected:
        failures.append({'aggregate_import_mismatch': sorted(aggregate ^ expected)})
    checked = [ROOT / 'NarrowDNF.lean', *sources,
               *sorted((ROOT / 'Verification').glob('*.lean')),
               *sorted((ROOT / 'scripts').glob('*.lean'))]
    challenge = ROOT / 'Verification/Challenge.lean'
    for path in checked:
        code = code_only(path.read_text())
        forbidden = r'\b(?:sorry|admit|axiom|unsafe|implemented_by|native_decide)\b'
        holes = 0
        for match in re.finditer(forbidden, code):
            if path == challenge and match.group() == 'sorry':
                holes += 1
            else:
                failures.append({'file': str(path.relative_to(ROOT)),
                                 'token': match.group(),
                                 'line': code[:match.start()].count('\n') + 1})
        if path == challenge and holes != 3:
            failures.append({'challenge_placeholder_count': holes, 'expected': 3})
        if path != challenge and 'Verification.Challenge' in imports(path.read_text()):
            failures.append({'challenge_import': str(path.relative_to(ROOT))})
    model_imports = imports((ROOT / 'Verification/Model.lean').read_text())
    if not model_imports or any(not name.startswith('Mathlib.') for name in model_imports):
        failures.append({'model_imports': 'must import only foundational Mathlib modules'})
    if imports(challenge.read_text()) != {'Verification.Model'}:
        failures.append({'challenge_imports': 'must import only Verification.Model'})
    if imports((ROOT / 'Verification/Solution.lean').read_text()) != {'NarrowDNF.Paper'}:
        failures.append({'solution_imports': 'must import only NarrowDNF.Paper'})
    config = json.loads((ROOT / 'Verification/config.json').read_text())
    targets = {'NarrowDNF.Verification.' + name for name in
               ['theorem_1_2', 'lemma_2_1', 'conjecture_1_1']}
    if set(config['theorem_names']) != targets or config.get('definition_names'):
        failures.append({'comparator_targets': 'unexpected targets or definition holes'})
    if set(config['permitted_axioms']) != {'propext', 'Classical.choice', 'Quot.sound'}:
        failures.append({'comparator_axioms': 'unexpected whitelist'})
    print(json.dumps({'proof_modules': len(sources), 'failures': failures}, indent=2))
    return bool(failures)


if __name__ == '__main__':
    sys.exit(main())
