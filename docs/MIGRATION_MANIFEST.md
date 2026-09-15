# Migration Manifest

HigherRankKUM has two distinct source relationships with `afletcher22/Rank3KUM`:

1. generic higher-rank infrastructure was migrated/refactored from `31ade8d073d7bedbf03b49612a76cea74dbc3b58` (`higher-rank-gluing-experiment`);
2. the completed rank-three proof is vendored immutably from `eff642a2e01fac4fc1f6f76e592eeea46c3152c9` (`version-3` at selection time).

Rank3KUM is not a live build dependency.

## Generic core

| Rank3KUM source | Status | HigherRankKUM destination | Notes |
|---|---|---|---|
| `UniformDensity.lean` — generic density/tight declarations | REFACTORED | `HigherRankKUM/Density.lean` | Rank-three tight classification left out of generic core. |
| `CyclicOrder.lean` — cyclic indexing | REFACTORED | `HigherRankKUM/CyclicIndex.lean` | Detached from `TwoGap.Final`. |
| `GenericGluing.lean` — `cyclicWindow`, generic cyclic order | REFACTORED | `HigherRankKUM/CyclicOrder.lean` | Generic interface has no rank-three dependency. |
| `TightContraction.lean` | MIGRATED | `HigherRankKUM/TightContraction.lean` | Rank-independent contraction bookkeeping. |
| `GenericGluing.lean` — gluing + tight factors | MIGRATED | `HigherRankKUM/GenericGluing.lean` | Generic theorem layer. |
| `BalancedInterleaveGeneral.lean` | MIGRATED | `HigherRankKUM/BalancedInterleave.lean` | Arbitrary positive `s,t,k`. |
| `BalancedWindowGeneral.lean` | MIGRATED | `HigherRankKUM/BalancedWindow.lean` | Left-start schedule arithmetic. |
| `BalancedWindowRightGeneral.lean` | MIGRATED | `HigherRankKUM/BalancedWindowRight.lean` | Right-start schedule arithmetic. |
| `BalancedWindowDecompositionGeneral.lean` | MIGRATED | `HigherRankKUM/BalancedWindowDecomposition.lean` | Full balanced window decomposition. |
| `BalancedGluingGeneral.lean` | MIGRATED | `HigherRankKUM/BalancedGluing.lean` | Arbitrary-rank restriction/contraction gluing. |
| `TightFactorReductionGeneral.lean` | REFACTORED | `HigherRankKUM/DivisibleSolver.lean`, `HigherRankKUM/TightFactorReduction.lean` | Abstract solver separated from concrete low ranks. |
| `TightInductionGeneral.lean` | REFACTORED | `HigherRankKUM/TightInduction.lean` | Arbitrary-rank proper-tight induction. |

## Low-rank bases

| Source mathematics | Status | HigherRankKUM destination | Notes |
|---|---|---|---|
| Rank-one part of `LowRankCyclicGeneral.lean` | INTERNALIZED | `HigherRankKUM/LowRank/RankOne.lean` | Standalone native proof. |
| Rank-two HalfWeave route | INTERNALIZED / COMPRESSED | `HigherRankKUM/LowRank/RankTwo*` | Minimal five-module implementation; legacy sorted-block machinery omitted. |
| Complete rank-three v3 proof | VENDORED IMMUTABLY | `vendor/Rank3KUM/` | Byte-for-byte snapshot of `eff642a2...`; original namespace retained. |
| Generic bridge from `CyclicBasisOrder3` | ADAPTED | `HigherRankKUM/LowRank/RankThree.lean` | Exposes `solvesDivisibleKUMAtRank_three`. |

The vendored `Rank3KUM/` source subtree has source and destination tree SHA

`a73e2f94c811a4f2f072e197d1a03656bc53f616`.

## Rank-four consequence

| Source idea | Status | HigherRankKUM destination | Notes |
|---|---|---|---|
| `RankFourTightCorollaryGeneral.lean` | REFACTORED / DISCHARGED | `HigherRankKUM/Rank4/TightReduction.lean` | Production proof uses generic lower-rank induction. Ranks 1,2,3 are all internally supplied; there are no solver hypotheses left. |
| old explicit `RankFourTightReduction.lean` | REFERENCE ONLY | historical comparison | The explicit `1+3`, `2+2`, `3+1` split is not the production architecture. |
| `HigherRankTightCorollaries.lean` | FUTURE RE-DERIVATION | future `HigherRankKUM/Consequences/` | Rank-5/6 consequences should use generic induction. |

## Rank-three proof machinery

The files under `vendor/Rank3KUM/` are deliberately frozen legacy source. They include `TwoGap`, `NearTightGeometry`, `StrictDensity`, `Splicing`, six-point machinery, `Version2`, and the final induction proof. They are **not** part of the generic HigherRankKUM architecture.

Only `HigherRankKUM/LowRank/RankThree.lean` may import the vendored library. New higher-rank proofs should not import rank-three internals directly.

## Infrastructure

- Lean: `leanprover/lean4:v4.33.0-rc2`.
- mathlib input revision: `v4.33.0-rc2`.
- `lake-manifest.json` pins resolved transitive dependencies.
- `vendor/Rank3KUM/SHA256SUMS` protects the frozen source snapshot.
- CI checks lockfile stability, vendor integrity, local-only Rank3KUM resolution, and the complete Lean build.

## Material intentionally excluded

Rank3KUM publication files, paper assets, Palomar metadata/scripts, challenge packaging, compression-history tooling, and Rank3KUM README/CITATION metadata are not vendored. HigherRankKUM copies the Lean proof source and license needed for the theorem base, not the old repository as a whole.

## Trusted dependency graph

```text
Lean / pinned mathlib
        ↓
HigherRankKUM generic core
        ↓
rank 1 ─ rank 2 ─ rank 3 adapter
                  ↓
          frozen local Rank3KUM v3
        ↓
proper-tight induction
        ↓
rank-4 and higher-rank research
```

There is no live edge from this graph to the external Rank3KUM repository.
