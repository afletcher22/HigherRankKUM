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

Ranks 1 and 2 are proved directly inside HigherRankKUM.

The rank-two theorem was internalized as a compressed HalfWeave development rather than as a dependency on the source repository. This is the preferred pattern when a source proof can be migrated without dragging in unrelated historical machinery.

Rank 3 should eventually be supplied internally in one of two acceptable ways:

1. **Native internal proof** — migrate/reorganize the certified proof into this repository while preserving its mathematical statement and provenance; or
2. **Vendored immutable snapshot** — copy the exact required certified source into this repository under a clearly marked vendor/legacy subtree, together with provenance and source commit hashes.

A live Git dependency on Rank3KUM is intentionally not an acceptable final architecture.

Until rank 3 is internalized, higher-rank theorems that require it take `SolvesDivisibleKUMAtRank α 3` as an explicit hypothesis. This keeps the trusted generic machinery fully self-contained and avoids introducing axioms.

## External dependencies

The initial migration uses only Lean/mathlib as external build dependencies:

- Lean: `v4.33.0-rc2`
- mathlib input revision: `v4.33.0-rc2`

`lake-manifest.json` records the exact resolved transitive package commits for the checkpoint. CI runs `lake update` and then requires the committed manifest to remain unchanged, detecting dependency-resolution drift.

## CI boundary checks

The main CI job verifies all of the following before accepting a build:

1. the pinned dependency graph resolves without changing `lake-manifest.json`;
2. trusted Lean modules contain no `Rank3KUM` import;
3. `lakefile.toml` contains no Rank3KUM dependency;
4. the HigherRankKUM library builds successfully.

## Provenance is not dependency

The original development history in Rank3KUM remains important for attribution, comparison, and auditing. `docs/PROVENANCE.md` and `docs/MIGRATION_MANIFEST.md` record those origins. That historical relationship must not be confused with a runtime or build dependency.
