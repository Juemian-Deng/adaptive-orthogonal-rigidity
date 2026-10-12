#!/usr/bin/env bash
# Run in a fresh checkout after installing the pinned official Lean toolchain
# and restoring the pinned mathlib cache (see docs/REPRODUCING.md).
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/verify_snapshot.py
version="$(lake env lean --version)"
case "$version" in
  'Lean (version 4.34.1,'*) ;;
  *) printf 'Wrong Lean version: %s\n' "$version" >&2; exit 1 ;;
esac
run=".verification/reproduce-$(date -u +%Y%m%dT%H%M%SZ)-$$"
mkdir -p "$run"
printf '%s\n' "$version" | tee "$run/toolchain.log"
python3 scripts/verify_dependencies.py | tee "$run/dependencies.log"
lake build 2>&1 | tee "$run/build.log"
lake env lean AdaptiveOrthogonalRigidity/TargetStatements.lean 2>&1 | tee "$run/contracts.log"
lake env lean verification/EndpointAxioms.lean 2>&1 | tee "$run/endpoint-axioms.log"
python3 - "$run/endpoint-axioms.log" <<'PY'
from pathlib import Path
import re
import sys
text = Path(sys.argv[1]).read_text()
blocks = re.findall(r'depends on axioms:\s*\[(.*?)\]', text, re.S)
assert len(blocks) == 5, f'Expected five endpoint axiom reports, got {len(blocks)}'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for block in blocks:
    assert {x.strip() for x in block.split(',') if x.strip()} <= allowed, block
print('All five main endpoint axiom reports use only the three standard axioms.')
PY
printf 'Reproduction logs: %s\n' "$run"
