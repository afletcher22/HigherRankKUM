# Dependency Policy

HigherRankKUM is intended to remain buildable and mathematically stable even if `afletcher22/Rank3KUM` later changes, is reorganized, or disappears.

## Hard rule

The trusted HigherRankKUM Lean tree must not depend on a live Rank3KUM branch, tag, release, or repository path.

In particular:

- no `import Rank3KUM...` statements are permitted in `HigherRankKUM/`;
- Rank3KUM must not appear as a Lake dependency;
- higher-rank theorems must not rely on mutable branch names from Rank3KUM;
- references to Rank3KUM in documentation are provenance only, not build dependencies.

CI enforces the import boundary.

## Low-rank solver policy

Rank 1 is proved directly inside HigherRankKUM.

Ranks 2 and 3 should eventually be supplied internally in one of two acceptable ways:

1. **Native internal proof** — migrate or reprove the minimal certified low-rank solver inside the HigherRankKUM namespace; or
2. **Vendored immutable snapshot** — copy the exact required certified source into this repository under a clearly marked vendor/legacy subtree, together with provenance and source commit hashes.

A live Git dependency on Rank3KUM is intentionally not an acceptable final architecture.

Until ranks 2 and 3 are internalized, generic higher-rank theorems should take `SolvesDivisibleKUMAtRank` certificates as explicit hypotheses. This keeps the trusted generic machinery fully self-contained and avoids introducing axioms.

## External dependencies

The initial migration uses only Lean/mathlib as external build dependencies:

- Lean: `v4.33.0-rc2`
- mathlib input revision: `v4.33.0-rc2`

`lake-manifest.json` records the exact resolved transitive package commits for the checkpoint.

## Provenance is not dependency

The original development history in Rank3KUM remains important for attribution, comparison, and auditing. `docs/PROVENANCE.md` and `docs/MIGRATION_MANIFEST.md` record those origins. That historical relationship must not be confused with a runtime or build dependency.
