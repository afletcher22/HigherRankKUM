# Dependency Policy

HigherRankKUM is intended to remain buildable and mathematically stable even if `afletcher22/Rank3KUM` later changes, is reorganized, or disappears.

## Hard rule

The trusted HigherRankKUM development must not depend on a live Rank3KUM branch, tag, release, or repository path.

In particular:

- Rank3KUM must not appear as an external Lake/Git dependency;
- higher-rank theorems must not rely on mutable Rank3KUM refs;
- the generic HigherRankKUM core must not import rank-three-specific proof machinery;
- documentation links to Rank3KUM are provenance only.

## Frozen local rank-three base

The completed rank-three theorem is available through a vendored immutable source snapshot at `vendor/Rank3KUM/`.

The snapshot was copied byte-for-byte from:

- repository `afletcher22/Rank3KUM`;
- branch `version-3` at selection time;
- commit `eff642a2e01fac4fc1f6f76e592eeea46c3152c9`;
- `Rank3KUM/` tree `a73e2f94c811a4f2f072e197d1a03656bc53f616`.

It is registered as a **local** Lake library with `srcDir = "vendor/Rank3KUM"`. No network access to Rank3KUM is needed to build HigherRankKUM after checkout.

Only `HigherRankKUM/LowRank/RankThree.lean` may import the vendored `Rank3KUM` namespace. That adapter exposes the narrow generic certificate

`solvesDivisibleKUMAtRank_three : SolvesDivisibleKUMAtRank α 3`.

Higher-rank modules depend on that certificate, not on the internal rank-three architecture.

## Low-rank solver policy

- Rank 1 is proved directly inside HigherRankKUM.
- Rank 2 is proved directly inside HigherRankKUM through the compressed HalfWeave implementation.
- Rank 3 is internal through the frozen vendored v3 source plus the narrow adapter above.

Thus all lower-rank inputs required by the divisible rank-four proper-tight reduction are locally available.

## Integrity checks

The vendored directory is treated as immutable legacy source.

- `vendor/Rank3KUM/SOURCE.md` records its exact origin.
- `vendor/Rank3KUM/SHA256SUMS` records hashes for all vendored Lean files.
- CI verifies those hashes.
- CI rejects `Rank3KUM` imports anywhere in `HigherRankKUM/` except `LowRank/RankThree.lean`.
- CI rejects a live Git dependency on Rank3KUM.

If the vendored base is ever intentionally upgraded, it should be done as an explicit snapshot replacement with new source commit/tree provenance and a fresh integrity manifest—not by following a branch.

## External dependencies

The build's external dependency surface is Lean/mathlib:

- Lean: `v4.33.0-rc2`;
- mathlib input revision: `v4.33.0-rc2`.

`lake-manifest.json` records the exact resolved transitive package commits.
