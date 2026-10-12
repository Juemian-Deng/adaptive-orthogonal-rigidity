#!/usr/bin/env python3
"""Verify the checked-source snapshot, without importing Lean or changing files."""
from pathlib import Path
import hashlib
import json
import sys

root = Path(__file__).resolve().parent.parent
manifest = root / 'verification/source-manifest.json'
expected = 'afed2e414a8c8bc755a86ee5e5d30953a76173b0b46e887beb771173fe9b8dc7'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
if sha(manifest) != expected:
    sys.exit('ERROR: source manifest identity does not match the selected snapshot')
m = json.loads(manifest.read_text())
seen = set()
for entry in m['source_files']:
    rel = Path(entry['path'])
    if rel.is_absolute() or '..' in rel.parts or str(rel) in seen:
        sys.exit(f'ERROR: invalid or duplicate manifest path: {rel}')
    seen.add(str(rel))
    path = root / rel
    if not path.is_file() or sha(path) != entry['sha256']:
        sys.exit(f'ERROR: missing or changed checked source: {rel}')
print(f"Verified checkpoint {m['checkpoint']}: {len(seen)} checked files")
print(f'Manifest SHA-256: {expected}')
print('This is source identity verification, not proof or semantic verification.')
