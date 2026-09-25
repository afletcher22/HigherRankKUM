# Local patches to the vendored Rank3KUM snapshot

The snapshot in this directory was copied byte-for-byte from `afletcher22/Rank3KUM` commit
`eff642a2e01fac4fc1f6f76e592eeea46c3152c9` (see `SOURCE.md`). It is otherwise frozen. The only
changes are the patches listed here, each needed to build on a newer pinned toolchain. None
changes a statement or a proof idea.

`SHA256SUMS` records the hashes of the patched files. To recover the pristine snapshot, apply the
patches below in reverse (`git apply -R`).

| Patch | Reason | Files |
|---|---|---|
| `patches/0001-mathlib-v4.35-equivOfEq.patch` | Toolchain upgrade to Lean/Mathlib `v4.35.0-rc3`, required for Palomar Registry submission (toolchain floor `v4.35.0-rc2`). Mathlib renamed `Equiv.setCongr` (equal sets are equivalent as types) to `Set.equivOfEq`, and `Equiv.setCongr_apply` to `Set.equivOfEq_apply`; the old name `Equiv.setCongr` now means the equivalence `Set α ≃ Set β` induced by `α ≃ β`. The patch is that mechanical rename at 13 sites. | `BalancedGluing.lean`, `ContractInterleave.lean`, `Interleave.lean`, `Splicing.lean`, `TightFlatAutomatic.lean` (all under `Rank3KUM/`) |
