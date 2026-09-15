# Provenance

`HigherRankKUM` is a research successor to `afletcher22/Rank3KUM`, not a fork and not a replacement for the rank-three proof artifact.

## Primary migration source

- Source repository: `afletcher22/Rank3KUM`
- Source branch: `higher-rank-gluing-experiment`
- Source commit: `31ade8d073d7bedbf03b49612a76cea74dbc3b58`
- Source tree: `45c7020a7c4232797ecd8c2c872db4f348c08baf`
- Lean toolchain at source: `leanprover/lean4:v4.33.0-rc2`
- mathlib revision at source: `v4.33.0-rc2`

This checkpoint contains the furthest higher-rank generalization work found in the Rank3KUM repository at migration time, including the arbitrary-rank restriction/contraction gluing machinery and the generic tight-set induction reduction.

## Supporting source checkpoints

- `generic-gluing-ablation` head: `22af08319c3489c49d1c5c6d874c2b81c8e57660`
  - Used as supporting evidence about which gluing machinery survives independently of the rank-three proof architecture.
- `version-3` head at migration audit: `eff642a2e01fac4fc1f6f76e592eeea46c3152c9`
  - This branch is treated as the publication/Palomar line for Rank3KUM, not as the source of higher-rank research code.

## Migration principle

The new repository should contain only machinery that is genuinely useful for higher-rank KUM research.

Rank-three-specific proof machinery remains in `Rank3KUM`. HigherRankKUM may depend on a pinned Rank3KUM theorem adapter when it needs the already-proved rank-three result as an induction base, but the generic core should not import rank-three-specific modules.

## Namespace policy

Migrated declarations should live under `HigherRankKUM`, even when their first implementation originated under `Rank3KUM`. This makes the dependency boundary explicit and prevents the research successor from masquerading as an extension of the old namespace.

## Reproducibility rule

Every copied or rewritten theorem should retain a traceable source entry in `docs/MIGRATION_MANIFEST.md`. If a theorem is materially rewritten during migration, the manifest should record both its Rank3KUM source declaration and its new HigherRankKUM declaration.
