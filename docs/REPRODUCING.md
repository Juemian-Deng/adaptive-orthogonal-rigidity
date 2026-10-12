# Reproducing the proofs

## Versions and scope

Use the official Lean release selected by `lean-toolchain` (4.34.1), the committed
`lakefile.toml`, and the committed `lake-manifest.json`. The manifest locks mathlib
at `d13f23b723b8a846827a245b89c10fc7d3f11612` and its transitive packages.
Do not run `lake update` or replace a lockfile as part of reproducing this snapshot.

Only files listed in `verification/source-manifest.json` are checked mathematical
sources/configuration. Documentation and reproduction tooling are outside that
mathematical snapshot and do not change a theorem. Development probes, obsolete
checkpoints, generated objects, and toolchain binaries are not needed in a release.

## Fresh checkout

1. Install the official Lean toolchain, normally with the official `elan` manager.
   The repository's `lean-toolchain` selects the required release automatically.
2. Start from a new checkout without project-owned `.olean` or `.ilean` files.
3. Run `lake exe cache get` to obtain the cache for the pinned mathlib version.
   This needs access to the official package and cache services.
4. Run `bash scripts/reproduce.sh`.

The script checks every frozen source hash, rejects a different Lean version,
builds the project, proves the five fully quantified manuscript contracts, and
checks the five actual endpoint axiom reports. Logs are written to a new local
`.verification/reproduce-*` directory. A Lean compilation error or unexpected
axiom causes a nonzero exit status.

The supplied proof terms use classical mathematics: the accepted foundational
axioms are `propext`, `Classical.choice`, and `Quot.sound`. No extra axiom,
`sorryAx`, or evaluation-based proof escape is permitted.

## Independent verification

The independent audit additionally recompiles every own source module in a
separate object directory, checks all theorem dependency closures, expands the
original graph law/events and numerical constants in separate endpoint
contracts, verifies the source/toolchain/package identities, and records linter
warnings. A cache hit in an incremental local build is not described as a clean
recompilation.

Checkpoint 033 has passed the independent audit described in
[the audit summary](INDEPENDENT_AUDIT.md), with a machine-readable record in
`verification/INDEPENDENT_AUDIT_RECEIPT.json`. One complete fresh project build
was bound to the immutable remote source by byte-for-byte verification. Remote
contracts and closure checks reused only those hash-bound auditor-built objects.

The independent auditor reviewed `scripts/reproduce.sh` statically and checked
its shell syntax, paths, dependency lock, targets, and failure propagation, and
executed its source/dependency identity checks separately. The full public
script was not run end-to-end by the auditor: its `lake build` would duplicate
the already completed fresh build. This is not a claim that the complete public
reproduction command has itself been end-to-end validated. The exact source
contracts and proof checks remain executable by readers.

## Existing project-local official toolchain

In the development workspace only, the same official binaries are installed at
`.toolchain/lean-4.34.1-linux/bin`. They can be selected by adding that directory
to `PATH`; it is not included in the source delivery. The Linux `lean` binary
used for the recorded local runs has SHA-256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Other supported operating systems use the same release, with different binary
hashes. The Lean source release and package lock remain the reproducibility
requirements across platforms.
