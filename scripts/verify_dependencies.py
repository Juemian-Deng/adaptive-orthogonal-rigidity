#!/usr/bin/env python3
"""Check installed package commits against the immutable Lake lockfile."""
from pathlib import Path
import json
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
lock = json.loads((root / 'lake-manifest.json').read_text())
for entry in lock['packages']:
    name, expected = entry['name'], entry['rev']
    dep = root / '.lake/packages' / name
    if not dep.is_dir():
        sys.exit(f'Missing package {name}; restore the pinned dependencies first.')
    actual = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], text=True).strip()
    dirty = subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
    if actual != expected or dirty:
        sys.exit(f'Package identity failed for {name}: commit {actual}, tracked changes {dirty!r}')
    print(f'{name}: {actual}, tracked source clean')
