# HigherRankKUM

HigherRankKUM is a research repository for extending the Kajitani–Ueno–Miyano cyclic basis-ordering program beyond the completed rank-three case.

It is a successor to [`afletcher22/Rank3KUM`](https://github.com/afletcher22/Rank3KUM), not a fork or replacement for that proof artifact. The initial codebase extracts the furthest genuinely higher-rank machinery developed during the Rank3KUM project and reorganizes it so the generic core has no hidden dependence on rank-three geometry.

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
- an independent rank-one divisible KUM solver.

The migration source and declaration-level policy are recorded in `docs/PROVENANCE.md` and `docs/MIGRATION_MANIFEST.md`.

## Rank-four program

Rank four has three arithmetic regimes:

1. `gcd(|E|,4)=1` — the coprime regime;
2. `gcd(|E|,4)=2`, equivalently `|E| ≡ 2 (mod 4)`;
3. `4 | |E|` — the divisible regime addressed by the present `r*k` machinery.

Inside the divisible regime, once ranks 1–3 are available internally through the solver interface, every instance with a nonempty proper tight set follows from generic induction. The remaining divisible structural target is therefore the strictly uniformly dense branch.

The `gcd=2` regime is a separate full-rank-four target and must not be conflated with the strict divisible branch. See `docs/RANK4_COVERAGE.md`.

## Repository policy

HigherRankKUM is intended to remain stable on its own even if Rank3KUM changes later.

- The trusted Lean tree must not import Rank3KUM.
- Rank3KUM is provenance, not a build dependency.
- Rank 1 is proved directly here.
- Ranks 2 and 3 will eventually be supplied by native internal proofs or by a clearly marked vendored immutable snapshot, not by a live Git dependency.
- Until then, generic higher-rank theorems take low-rank solver certificates explicitly.

See `docs/DEPENDENCY_POLICY.md`.

Experimental rank-four searches and candidate lemmas should remain separated from the trusted generic dependency graph until their mathematical role is understood.

## Toolchain

The initial migration checkpoint preserves the source environment:

- Lean `v4.33.0-rc2`
- mathlib `v4.33.0-rc2`

The committed Lake manifest pins the resolved transitive dependency graph for reproducibility.
