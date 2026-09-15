# Migration Manifest

Source checkpoint: `afletcher22/Rank3KUM@31ade8d073d7bedbf03b49612a76cea74dbc3b58` (`higher-rank-gluing-experiment`).

The status labels mean:

- **COPY** — mathematically and architecturally rank-independent; migrate with only namespace/import cleanup.
- **REFACTOR** — contains genuinely reusable mathematics but is coupled to rank-three modules or mixes generic and rank-specific declarations.
- **REFERENCE** — useful as a model, regression oracle, or base theorem, but should remain in Rank3KUM.
- **DROP** — publication, Palomar, compression-history, or obsolete duplicate material that does not belong in the HigherRankKUM core.

## Generic core

| Rank3KUM source | Status | HigherRankKUM destination | Notes |
|---|---|---|---|
| `UniformDensity.lean` — `UniformlyDense`, `Tight`, `UniformlyDense.restrict`, `tight_isFlat`, `loopless_of_uniformlyDense` | REFACTOR | `HigherRankKUM/Density.lean` | Copy the generic declarations only. Leave `tight_rank_one_or_two`, rank-three tight cardinality lemmas, and rank-three classification behind. |
| `CyclicOrder.lean` — `cyclicIndex` and elementary cyclic-index lemmas | REFACTOR | `HigherRankKUM/CyclicIndex.lean` | The file currently imports `TwoGap.Final`; do not copy the file wholesale. Extract only the rank-neutral indexing API. |
| `GenericGluing.lean` — `cyclicWindow`, `CyclicBasisOrder` | REFACTOR | `HigherRankKUM/CyclicOrder.lean` | Move the generic predicate/interface out of the old gluing module so it has no rank-three dependency. |
| `TightContraction.lean` | COPY | `HigherRankKUM/TightContraction.lean` | `eRk_union_eq_contract_eRk_add`, `isBase_union_of_isBasis_contract_isBase`, and `UniformlyDense.contract_tight` are rank-independent. |
| `GenericGluing.lean` — gluing theorem and `UniformlyDense.tight_factors` | COPY | `HigherRankKUM/GenericGluing.lean` | Keep after the cyclic-order interface has been separated. |
| `BalancedInterleaveGeneral.lean` | COPY | `HigherRankKUM/BalancedInterleave.lean` | Pure schedule/indexing machinery for arbitrary positive `s,t,k`. |
| `BalancedWindowGeneral.lean` | COPY | `HigherRankKUM/BalancedWindowLeft.lean` | Arbitrary-rank balanced-window arithmetic. |
| `BalancedWindowRightGeneral.lean` | COPY | `HigherRankKUM/BalancedWindowRight.lean` | Arbitrary-rank balanced-window arithmetic. |
| `BalancedWindowDecompositionGeneral.lean` | COPY | `HigherRankKUM/BalancedWindowDecomposition.lean` | Establishes the full `(L^s R^t)^k` window decomposition. |
| `BalancedGluingGeneral.lean` | COPY | `HigherRankKUM/BalancedGluing.lean` | Concrete arbitrary-rank restriction/contraction gluing theorem. |
| `TightFactorReductionGeneral.lean` — `SolvesDivisibleKUMAtRank` and generic reduction | REFACTOR | `HigherRankKUM/DivisibleSolver.lean`, `HigherRankKUM/TightFactorReduction.lean` | Split the abstract solver predicate from concrete ranks 1–3. The generic reduction must not import Rank3KUM's proof stack. |
| `TightInductionGeneral.lean` | COPY/REFACTOR | `HigherRankKUM/TightInduction.lean` | Core theorem is fully arbitrary-rank. Rename namespace/imports and depend only on abstract solver interface + generic reduction. |

## Low-rank adapters

| Rank3KUM source | Status | HigherRankKUM destination | Notes |
|---|---|---|---|
| `LowRankCyclicGeneral.lean` — rank-one solver | REFACTOR | `HigherRankKUM/LowRank/RankOne.lean` | Generic proof; should be detached from HalfWeave/rank-three imports. |
| `LowRankCyclicGeneral.lean` — rank-two solver | REFACTOR | `HigherRankKUM/LowRank/RankTwo.lean` | Depends on Rank3KUM HalfWeave implementation. Initially use a thin adapter or copy only after deciding whether HalfWeave belongs as shared infrastructure. |
| `LowRankCyclicGeneral.lean` — rank-three solver | REFERENCE/ADAPTER | `HigherRankKUM/LowRank/RankThreeAdapter.lean` | Do not copy the rank-three proof. Import or otherwise pin the certified Rank3KUM theorem and translate it to the generic `CyclicBasisOrder` interface. |
| `TightFactorReductionGeneral.lean` — `solvesDivisibleKUMAtRank_one/two/three` | REFACTOR | `HigherRankKUM/LowRank/Solvers.lean` | Rebuild these as adapters over the isolated rank-one, rank-two, rank-three solver files. |

## First higher-rank consequences

| Rank3KUM source | Status | HigherRankKUM destination | Notes |
|---|---|---|---|
| `RankFourTightCorollaryGeneral.lean` | COPY after core | `HigherRankKUM/Rank4/TightReduction.lean` | Preferred rank-four non-strict theorem. It derives the result uniformly from lower-rank induction rather than a hand-split `1+3`, `2+2`, `3+1` proof. |
| `RankFourTightReduction.lean` | REFERENCE | `docs/RANK4_REGRESSION.md` | Keep as an independent explicit derivation for regression/comparison, not as production code. It imports rank-three `StrictDensity`, so it is a poor architectural base. |
| `HigherRankTightCorollaries.lean` | REFACTOR | `HigherRankKUM/Consequences/TightRanks.lean` | Rank-five tight ranks `2/3` and rank-six tight rank `3` are useful consequences, but the duplicated contraction-rank bookkeeping should use the generic theorem from `TightInduction`. |

## Rank-three-specific machinery — reference only

The following should not be copied into the HigherRankKUM core at initial migration:

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

These remain valuable as proof-pattern references when searching for the rank-four strict branch, but copying them would blur the distinction between generic infrastructure and rank-three geometry.

## Infrastructure to preserve

- `lean-toolchain`: preserve `leanprover/lean4:v4.33.0-rc2` for the initial migration checkpoint.
- mathlib: preserve `v4.33.0-rc2` for the initial migration checkpoint.
- `.gitignore`: copy/adapt.
- CI: create a new minimal build workflow for HigherRankKUM rather than copying Rank3KUM's Palomar/compression-oriented workflow wholesale.

## Material to drop from initial migration

- `Challenge.lean`, `Solution.lean`, `formalization.yaml`, `comparator.json`
- Palomar scripts and metadata
- rank-three paper-alignment documents
- compression-baseline tooling unless later reused as a generic proof-maintenance tool
- `CITATION.cff` until HigherRankKUM has an independent citable release

## Dependency boundary

The intended dependency direction is:

```text
Mathlib
  ↓
HigherRankKUM generic core
  ↓
HigherRankKUM low-rank interfaces
  ↓                 ↘
Rank-one/two code     Rank3KUM pinned theorem adapter
  ↓                 ↙
Tight-set induction / higher-rank consequences
  ↓
Rank4 strict-branch research
```

The generic core must never import a Rank3KUM rank-three-specific module.
