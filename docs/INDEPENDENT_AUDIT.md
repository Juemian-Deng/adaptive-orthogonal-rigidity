# Independent audit of checkpoint 033

**Verdict: PASS for the four exact main endpoints and the sufficient block range.**
This records machine checking and an independent AI-assisted semantic audit; it
is not a claim of independent human peer review or formalization of every prose
statement in the manuscript.

## Immutable mathematical source

- Audited repository: `Juemian-Deng/adaptive-orthogonal-rigidity`, private at audit.
- Audited source commit: `03130bb08398ae4e08c3c8e6544086689b2588b2`.
- Git tree: `0375064cb9b2bf61bfaa58fd3fabede36551fd43`.
- Source manifest SHA-256:
  `afed2e414a8c8bc755a86ee5e5d30953a76173b0b46e887beb771173fe9b8dc7`.
- Mathematical source/configuration: 166 files, including 163 Lean modules.
- Lean 4.34.1; mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`;
  all nine dependency revisions were checked against the committed Lake lock.

A later documentation-only commit can carry this report without changing the
mathematical snapshot. The machine-readable evidence is in
[`verification/INDEPENDENT_AUDIT_RECEIPT.json`](../verification/INDEPENDENT_AUDIT_RECEIPT.json).

## What passed

All project modules were independently compiled into fresh objects, sharing only
pinned dependency caches. No implementation-worker project objects were used.
The audit covered 1,839 local declarations, 1,485 theorem roots and 45,507
transitive constants, with 736 explicit public named axiom checks and two model
regression proofs. Only `propext`, `Classical.choice` and `Quot.sound` occur in
proof closures. No `sorryAx`, custom axiom, or unsafe/partial proof dependency
occurs. A graph-matrix runtime helper lies outside those proof closures.

The five exact target contracts and independent expanded original-model
contracts passed: finite movement, both movement asymptotic conclusions, finite
support components including the geometric bound, support-component asymptotics,
and the sufficient cube-root/log range. The complete real-to-regular-F3
descriptor bridge was separately checked. The four final endpoint closures have
44,037, 44,278, 32,563 and 32,709 constants respectively.

The events use the original independent heterogeneous Bernoulli edge law, all
real orthogonal witnesses chosen after sampling, and ordinary permutation
isomorphism. Constants, finite sums and real exponents are retained. Asymptotic
error sequences and thresholds precede every admissible edge array. Neither
parameter sequence must be monotone or tend to infinity.

Eighteen previously accepted intermediate contract/closure checks were inherited
only where source and transitive dependency identities were unchanged. All
current project modules were nevertheless fresh-compiled. No new or main
endpoint contract was skipped. For efficiency, required contract bodies were
also checked together in isolated namespaces, with imports collected at the top
and no added hypotheses; original fragment and combined-source hashes are
recorded.

## Actual remote package and reproduction limits

The auditor independently fetched repository, commit and complete tree metadata,
then re-decoded all 183 remote files and checked their Git blob identities,
SHA-256 hashes, paths, sizes and modes. All 166 mathematical source/configuration
files exactly match the fresh-compiled snapshot. Actual remote target-contract
sources, public endpoint axiom checks, expanded contracts and full proof closures
were revalidated using only those hash-bound auditor-built objects. There was
one complete fresh project build, not two.

The public reproduction script passed static and shell-syntax review, including
relative paths, dependency locks, target selection, error propagation and absence
of hidden development-workspace requirements. Its identity checks were executed
separately. The complete `scripts/reproduce.sh` was **not** run end-to-end by the
independent auditor; its `lake build` would repeat the fresh compilation. A
pattern-based scan found no recognized credentials in the remote package; this
is not a guarantee against every possible secret encoding.

## Explicit coverage limits

The exact main conclusions are proved. Three wider standalone auxiliary forms
remain outside the claimed coverage: arbitrary-coordinate-distribution affine
fibers; the support lower bound for every ternary matrix; and general-field
global descent with the strict total-deletion bound. The proved Bernoulli,
minimum-relative-rank and original-graph budgeted specializations suffice for
the unchanged main conclusions. The standalone reflection-product corollary is
not included in checkpoint 033. See [the detailed coverage ledger](PROOF_COVERAGE.md).
