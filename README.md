# Adaptive orthogonal rigidity

Lean formalization of the two main results in *Quantitative rigidity of random
graphs under adaptive real orthogonal transformations* (12 October 2026).

## Verification status

All four exact finite and asymptotic main endpoints, plus the sufficient block
range, pass independent audit in checkpoint 033. The audit includes a fresh
compilation of all 163 project modules, expanded original-model contracts,
recursive proof-dependency checks, and verification of the actual remote source
bytes. See [the independent audit summary](docs/INDEPENDENT_AUDIT.md) for the
precise evidence, trust boundary, and limitations.

| Manuscript result | Lean declaration |
| --- | --- |
| Finite movement rank, `thm:finite` | `finite_movement_bound` |
| Movement asymptotics, both estimates, `thm:main` | `asymptotic_movement_bound` |
| Finite support components and geometric bound, `thm:block-finite` | `finite_block_bound` |
| Support-component asymptotics, `thm:blocks` | `asymptotic_block_bound` |
| Sufficient cube-root/log range | `sufficient_block_range` |

All names are in the namespace `AdaptiveOrthogonalRigidity`.
`TargetStatements.lean` proves five separate fully quantified endpoint contracts;
it no longer contains only proposition type checks.

The events use the original independent heterogeneous Bernoulli edge law,
ordinary permutation isomorphism, and arbitrary real orthogonal witnesses
selected after observing the entire sample. The asymptotic error sequences and
thresholds are chosen before every admissible edge-probability array.

The main endpoint coverage is distinct from literal formalization of every
auxiliary statement at its widest generality. See [the coverage ledger](docs/PROOF_COVERAGE.md)
for explicit specializations and the unformalized standalone reflection
corollary. No independent human peer review is claimed.

## Reproduce

- Lean: `leanprover/lean4:v4.34.1`
- mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Source snapshot: `verification/source-manifest.json`
- Manifest SHA-256: `afed2e414a8c8bc755a86ee5e5d30953a76173b0b46e887beb771173fe9b8dc7`

After setting up the pinned official toolchain and dependencies, run
`bash scripts/reproduce.sh`. See [clean reproduction instructions](docs/REPRODUCING.md).
All independently checked theorem proof closures use only `propext`,
`Classical.choice`, and `Quot.sound`. The complete public reproduction script
has not been executed end-to-end by the independent auditor; its static review,
identity checks, and separately executed proof checks are distinguished in the
[audit summary](docs/INDEPENDENT_AUDIT.md).

The repository was private when audited. Acceptance applies to the exact source
manifest above and the scope recorded in the independent audit summary.
