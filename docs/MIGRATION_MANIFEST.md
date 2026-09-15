# Migration Manifest

Source checkpoint: `afletcher22/Rank3KUM@31ade8d073d7bedbf03b49612a76cea74dbc3b58` (`higher-rank-gluing-experiment`).

This document records where HigherRankKUM's initial infrastructure came from. Rank3KUM is **provenance, not a build dependency**.

Status labels:

- **MIGRATED** — now lives in HigherRankKUM's trusted Lean tree.
- **REFACTORED** — reusable mathematics was separated from rank-three-specific dependencies during migration.
- **COMPRESSED MIGRATION** — the mathematical route was retained, but a smaller dependency slice was rebuilt instead of copying the full source subsystem.
- **INTERNALIZATION PENDING** — certified mathematics exists in the source project, but HigherRankKUM does not yet contain its own internal certified implementation.
- **REFERENCE ONLY** — retained as a proof-pattern/regression reference, not copied into the trusted tree.
- **DROP** — publication, Palomar, compression-history, or obsolete duplicate material that does not belong here.

## Generic core

| Rank3KUM source | Status | HigherRankKUM destination | Notes |
|---|---|---|---|
| `UniformDensity.lean` — generic density/tight declarations | REFACTORED | `HigherRankKUM/Density.lean` | Rank-three tight-set classification was intentionally left behind. |
| `CyclicOrder.lean` — `cyclicIndex` API | REFACTORED | `HigherRankKUM/CyclicIndex.lean` | Extracted away from the old `TwoGap.Final` import. |
| `GenericGluing.lean` — `cyclicWindow`, `CyclicBasisOrder` | REFACTORED | `HigherRankKUM/CyclicOrder.lean` | Generic cyclic-order language now has no rank-three dependency. |
| `TightContraction.lean` | MIGRATED | `HigherRankKUM/TightContraction.lean` | Rank-independent contraction rank/basis/density lemmas. |
| `GenericGluing.lean` — abstract gluing + tight factors | MIGRATED | `HigherRankKUM/GenericGluing.lean` | Kept after separating the cyclic-order interface. |
| `BalancedInterleaveGeneral.lean` | MIGRATED | `HigherRankKUM/BalancedInterleave.lean` | Arbitrary positive `s,t,k`. |
| `BalancedWindowGeneral.lean` | MIGRATED | `HigherRankKUM/BalancedWindow.lean` | Arbitrary-rank left-start schedule arithmetic. |
| `BalancedWindowRightGeneral.lean` | MIGRATED | `HigherRankKUM/BalancedWindowRight.lean` | Arbitrary-rank right-start schedule arithmetic. |
| `BalancedWindowDecompositionGeneral.lean` | MIGRATED | `HigherRankKUM/BalancedWindowDecomposition.lean` | Full `(L^s R^t)^k` decomposition. |
| `BalancedGluingGeneral.lean` | MIGRATED | `HigherRankKUM/BalancedGluing.lean` | Concrete arbitrary-rank restriction/contraction gluing. |
| `TightFactorReductionGeneral.lean` — abstract solver + reduction | REFACTORED | `HigherRankKUM/DivisibleSolver.lean`, `HigherRankKUM/TightFactorReduction.lean` | Abstract solver interface is separated from concrete low-rank implementations. |
| `TightInductionGeneral.lean` | REFACTORED | `HigherRankKUM/TightInduction.lean` | Arbitrary-rank tight-set induction now depends only on HigherRankKUM generic modules. |

## Low-rank bases

| Source mathematics | Status | HigherRankKUM destination | Policy |
|---|---|---|---|
| Rank-one part of `LowRankCyclicGeneral.lean` | MIGRATED | `HigherRankKUM/LowRank/RankOne.lean` | Fully internal and standalone. |
| Rank-two HalfWeave route | COMPRESSED MIGRATION | `HigherRankKUM/LowRank/RankTwo.lean` plus `LowRank/RankTwo/*` | Rebuilt from the minimal dependency slice needed by the direct proof; no Rank3KUM import and no legacy fully-sorted closure-block stack. |
| Completed rank-three theorem | INTERNALIZATION PENDING | future internal/vendored rank-three base | Must be made internally available without a live Rank3KUM dependency. |
| `solvesDivisibleKUMAtRank_one/two/three` wrappers | PARTIAL | current rank-one/rank-two modules; future rank-three base | Ranks 1 and 2 are internally discharged. Rank 3 remains an explicit solver hypothesis where needed. |

### Rank-two compression details

The source HalfWeave development spans a larger collection of files, including legacy stronger sorted-block infrastructure. HigherRankKUM keeps only the mathematical dependency slice used by the direct uniform-density proof:

- `LowRank/RankTwo/Indexing.lean` — cyclic half-weave indexing;
- `LowRank/RankTwo/LargestFirst.lean` — the weak largest-first contiguous-block condition and crossing lemmas;
- `LowRank/RankTwo/FinitePartition.lean` — generic finite-partition flattening with a largest block first;
- `LowRank/RankTwo/Matroid.lean` — singleton-closure partition, density bound, and adjacent-base theorem;
- `LowRank/RankTwo.lean` — bridge to the generic `CyclicBasisOrder` interface and `solvesDivisibleKUMAtRank_two`.

The stronger legacy `SortedBlockModel` route is intentionally not part of the migrated trusted tree.

No axioms are introduced to pretend the missing rank-three internalization is present.

## First higher-rank consequence

| Rank3KUM source | Status | HigherRankKUM destination | Notes |
|---|---|---|---|
| `RankFourTightCorollaryGeneral.lean` | REFACTORED | `HigherRankKUM/Rank4/TightReduction.lean` | Clean specialization of the generic theorem; ranks 1 and 2 are internal, so only the rank-3 solver certificate remains explicit. |
| `RankFourTightReduction.lean` | REFERENCE ONLY | documentation/regression reference | Explicit `1+3`, `2+2`, `3+1` derivation is not the production architecture. |
| `HigherRankTightCorollaries.lean` | FUTURE RE-DERIVATION | future `HigherRankKUM/Consequences/` | Rank-5/6 consequences should be recovered from the generic reduction rather than copied with duplicate bookkeeping. |

## Rank-three-specific machinery — reference only

The following is not part of the HigherRankKUM trusted tree:

- `TwoGap.lean` and `TwoGap/*`
- `NearTightGeometry.lean`
- `StrictDensity.lean`
- `SixPointCombinatorics.lean`
- `SixPointMatroid.lean`
- `Version2/*`
- `FinalInduction.lean`
- `FinalReduction.lean`
- `InductionStep.lean`
- `Splicing.lean`
- `SpliceWrap.lean`
- `ContractInterleave.lean`
- old rank-three `BalancedGluing.lean`

They remain useful as proof-pattern references when searching for rank-four machinery, but copying them wholesale would blur the boundary between generic infrastructure and rank-three geometry.

## Infrastructure

The initial migration checkpoint preserves:

- Lean `leanprover/lean4:v4.33.0-rc2`;
- mathlib input revision `v4.33.0-rc2`;
- the exact resolved transitive package commits in `lake-manifest.json`;
- a standalone CI boundary that rejects trusted `Rank3KUM` imports and detects lockfile drift.

## Material intentionally dropped

- `Challenge.lean`, `Solution.lean`, `formalization.yaml`, `comparator.json`
- Palomar scripts and metadata
- rank-three paper-alignment documents
- compression-baseline tooling unless later reused as a generic maintenance tool
- `CITATION.cff` until HigherRankKUM has an independent citable release

## Dependency boundary

The intended trusted dependency graph is now:

```text
Lean / pinned mathlib
        ↓
HigherRankKUM generic core
        ↓
internal rank-1 / rank-2 solvers
        ↓
conditional lower-rank induction (rank 3 still explicit where needed)
        ↓
rank-4 and higher-rank research
```

Rank3KUM is outside this graph. It appears only in provenance and research-reference documentation.

See `docs/DEPENDENCY_POLICY.md`.
