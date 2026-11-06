#!/usr/bin/env python3
"""Check bundled snapshot integrity and its actual theorem numbering."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent / 'paper'
manifest = json.loads((root / 'manifest.json').read_text())
for kind in ('source', 'pdf'):
    record = manifest[kind]
    data = (root / record['path']).read_bytes()
    assert len(data) == record['bytes'], f'{kind}: byte count mismatch'
    assert hashlib.sha256(data).hexdigest() == record['sha256'], f'{kind}: SHA-256 mismatch'

source = (root / manifest['source']['path']).read_text()
source = re.sub(r'(?<!\\)%[^\n]*', '', source)
section = counter = 0
numbering = {}
pattern = r'\\section\{|\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition|example|remark)\}'
for match in re.finditer(pattern, source):
    if match.group(1) is None:
        section += 1
        counter = 0
    else:
        counter += 1
        body = source[match.end():source.index('\\end{' + match.group(1) + '}', match.end())]
        label = re.search(r'\\label\{([^}]+)\}', body)
        assert label, 'Numbered result missing its stable TeX label'
        numbering[label.group(1)] = f'{section}.{counter}'
assert numbering == manifest['numbered_results'], f'Numbered-result mapping changed: {numbering}'
print(json.dumps({'status': 'PASS', 'source_sha256': manifest['source']['sha256'],
                  'numbered_results': numbering}, indent=2))
