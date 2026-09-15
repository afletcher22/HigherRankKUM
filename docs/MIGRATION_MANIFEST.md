# Migration Manifest

Source checkpoint: `afletcher22/Rank3KUM@31ade8d073d7bedbf03b49612a76cea74dbc3b58` (`higher-rank-gluing-experiment`).

This document records where HigherRankKUM's initial generic infrastructure came from. Rank3KUM is **provenance, not a build dependency**.

Status labels:

- **MIGRATED** — now lives in HigherRankKUM's trusted Lean tree.
- **REFACTORED** — reusable mathematics was separated from rank-three-specific dependencies during migration.
- **INTERNALIZATION PENDING** — certified low-rank mathematics exists in the source project but is not yet independently available inside HigherRankKUM.
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
| Rank-two HalfWeave route | INTERNALIZATION PENDING | future `HigherRankKUM/LowRank/RankTwo.lean` | Must be proved internally or vendored immutably; no live Rank3KUM dependency. |
| Completed rank-three theorem | INTERNALIZATION PENDING | future internal/vendored rank-three base | Must be made internally available without a live Rank3KUM dependency. |
| `solvesDivisibleKUMAtRank_one/two/three` wrappers | PARTIAL | future `HigherRankKUM/LowRank/Solvers.lean` | Rank 1 can be discharged now; ranks 2–3 remain explicit solver hypotheses until internalized. |

No axioms are introduced to pretend the missing low-rank internalizations are present.

## First higher-rank consequence

| Rank3KUM source | Status | HigherRankKUM destination | Notes |
|---|---|---|---|
| `RankFourTightCorollaryGeneral.lean` | REFACTORED | `HigherRankKUM/Rank4/TightReduction.lean` | Clean specialization of the generic theorem; rank-2 and rank-3 solver certificates remain explicit hypotheses. |
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
internal low-rank solver interface
        ↓
conditional / discharged tight-set induction
        ↓
rank-4 and higher-rank research
```

Rank3KUM is outside this graph. It appears only in provenance and research-reference documentation.

See `docs/DEPENDENCY_POLICY.md`.
