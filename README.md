# HigherRankKUM

HigherRankKUM is a research repository for extending the Kajitani–Ueno–Miyano cyclic basis-ordering program beyond the completed rank-three case.

It is a successor to [`afletcher22/Rank3KUM`](https://github.com/afletcher22/Rank3KUM), not a fork or replacement for that proof artifact. The higher-rank core has been reorganized so its generic machinery is independent of rank-three geometry, while the completed rank-three proof is retained locally as a frozen vendored base theorem.

## Current formal core

The repository currently contains:

- arbitrary-rank cyclic-window and cyclic-basis-order definitions;
- uniform density and tight-set infrastructure;
- restriction and tight-contraction density inheritance;
- abstract restriction/contraction basis gluing;
- arbitrary-rank balanced `(L^s R^t)^k` interleaving;
- a concrete balanced restriction/contraction gluing theorem;
- an abstract `SolvesDivisibleKUMAtRank` interface;
- generic tight-factor reduction;
- the theorem reducing every divisible rank-`r` instance with a nonempty proper tight set to solved lower ranks;
- internal divisible KUM solvers at ranks 1 and 2;
- an internal rank-3 solver backed by a frozen vendored copy of the Rank3KUM version-3 proof.

The migration source and declaration-level policy are recorded in `docs/PROVENANCE.md`, `docs/MIGRATION_MANIFEST.md`, and `docs/DEPENDENCY_POLICY.md`.

## Vendored rank-three theorem

`vendor/Rank3KUM/` is a Lean-source snapshot of the following commit. It is byte-for-byte except for toolchain patches, which are listed in `vendor/Rank3KUM/PATCHES.md`:

- source repository: `afletcher22/Rank3KUM`;
- source branch at selection time: `version-3`;
- exact source commit: `eff642a2e01fac4fc1f6f76e592eeea46c3152c9`;
- exact source `Rank3KUM/` tree: `a73e2f94c811a4f2f072e197d1a03656bc53f616`.

The snapshot is a local Lake library, not a Git dependency. `HigherRankKUM/LowRank/RankThree.lean` is the only HigherRankKUM module allowed to import it and exposes the narrow theorem `solvesDivisibleKUMAtRank_three`.

`vendor/Rank3KUM/SHA256SUMS` records checksums for the vendored Lean source as patched. CI verifies those checksums and the exact source commit recorded in `vendor/Rank3KUM/SOURCE.md`.

## Rank-four program

Rank four has three arithmetic regimes:

1. `gcd(|E|,4)=1` — the coprime regime;
2. `gcd(|E|,4)=2`, equivalently `|E| ≡ 2 (mod 4)`;
3. `4 | |E|` — the divisible regime addressed by the present `r*k` machinery.

Within the divisible regime, ranks 1–3 are now internally available. Therefore every rank-four instance with a nonempty proper tight set is formally discharged by the generic lower-rank induction theorem. The remaining new structural target there is the strictly uniformly dense branch.

The `gcd=2` regime is a separate full-rank-four target and must not be conflated with the strict divisible branch. See `docs/RANK4_COVERAGE.md`.

## Repository policy

HigherRankKUM is intended to remain stable on its own even if Rank3KUM later changes, is reorganized, or disappears.

- There is no live Git dependency on Rank3KUM.
- Rank3KUM is provenance plus a frozen local source snapshot.
- Only `HigherRankKUM/LowRank/RankThree.lean` may import the vendored `Rank3KUM` library.
- The generic core must remain independent of rank-three-specific proof machinery.
- Experimental rank-four searches and candidate lemmas remain outside the trusted dependency graph until their mathematical role is understood.

## Toolchain

The project is pinned to:

- Lean `v4.35.0-rc3`;
- mathlib `v4.35.0-rc3`;
- the exact resolved transitive dependency graph in `lake-manifest.json`.

The initial migration used `v4.33.0-rc2`. The upgrade to `v4.35.0-rc3` meets the Palomar Registry
toolchain floor (`v4.35.0-rc2`). It needed only the Mathlib rename `Equiv.setCongr` →
`Set.equivOfEq`, which touches 8 sites in HigherRankKUM and 13 in the vendored snapshot (see
`vendor/Rank3KUM/PATCHES.md`).
