# Provenance

`HigherRankKUM` is a research successor to `afletcher22/Rank3KUM`, not a fork and not a replacement for the rank-three proof artifact.

## Generic migration source

The initial higher-rank infrastructure was extracted from:

- source repository: `afletcher22/Rank3KUM`;
- source branch: `higher-rank-gluing-experiment`;
- source commit: `31ade8d073d7bedbf03b49612a76cea74dbc3b58`;
- source tree: `45c7020a7c4232797ecd8c2c872db4f348c08baf`;
- Lean toolchain: `leanprover/lean4:v4.33.0-rc2`;
- mathlib: `v4.33.0-rc2`.

That checkpoint contained the arbitrary-rank restriction/contraction gluing machinery and generic tight-set induction that were subsequently separated from rank-three-specific imports.

## Frozen rank-three base

The completed rank-three proof is separately vendored from the publication/Palomar line:

- source repository: `afletcher22/Rank3KUM`;
- source branch at selection time: `version-3`;
- exact source commit: `eff642a2e01fac4fc1f6f76e592eeea46c3152c9`;
- source commit tree: `05ec48559859c6f64d90cbac38b352c287fdf503`;
- exact source `Rank3KUM/` subtree: `a73e2f94c811a4f2f072e197d1a03656bc53f616`;
- source root `Rank3KUM.lean` blob: `d5772bbc9f798d202ddd41af84b928dab67e91d4`.

When it was vendored, the directory `vendor/Rank3KUM/Rank3KUM/` had the same Git tree SHA `a73e2f94c811a4f2f072e197d1a03656bc53f616`. This gave direct Git-level confirmation that the Lean source subtree was byte-for-byte identical to the selected v3 source. The root source and license were copied alongside it. The toolchain patches in `vendor/Rank3KUM/PATCHES.md` have changed that tree since. Reversing them (`git apply -R`) restores the original tree.

`vendor/Rank3KUM/SOURCE.md` and `vendor/Rank3KUM/SHA256SUMS` make this origin and integrity independently auditable inside HigherRankKUM.

## Supporting historical checkpoints

- `generic-gluing-ablation` head `22af08319c3489c49d1c5c6d874c2b81c8e57660` was used when auditing which gluing machinery survives independently of the rank-three proof architecture.
- Rank3KUM `version-3` remains the publication/Palomar line. Later edits there do not alter HigherRankKUM's frozen snapshot unless an explicit vendor upgrade is performed.

## Namespace and dependency policy

Generic declarations live under `HigherRankKUM`. The vendored legacy source deliberately retains its original `Rank3KUM` namespace so it can remain unchanged. A single adapter, `HigherRankKUM/LowRank/RankThree.lean`, translates the completed rank-three theorem into HigherRankKUM's generic solver interface.

Rank3KUM is therefore historical provenance and frozen local source, **not a live build dependency**.

Every migrated or adapted theorem should remain traceable through `docs/MIGRATION_MANIFEST.md`.
