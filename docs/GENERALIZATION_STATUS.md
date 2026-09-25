# Generalization Status

This file distinguishes certified generic infrastructure from rank-specific results and open research targets.

## Status vocabulary

- **Formalized generic** — Lean theorem has no fixed ambient-rank hypothesis and lives in the HigherRankKUM generic dependency chain.
- **Formalized internal** — the required result is proved inside this repository (including the frozen local Rank3KUM snapshot) without a live external proof dependency.
- **Formalized conditional** — Lean verifies the reduction, but an explicitly stated solver or literature theorem remains a hypothesis.
- **Computational evidence** — exact finite certificate, not a universal theorem.
- **Research target** — no proof is currently present in HigherRankKUM.

## Formalized generic infrastructure

HigherRankKUM contains arbitrary-rank formalizations of:

- integer uniform density `UniformlyDense` and tightness `Tight`;
- rational/cross-multiplied density `UniformlyDenseRatio` and `TightRatio`;
- restriction and tight-contraction density inheritance;
- tight sets as flats under the relevant finite positive-density hypotheses;
- looplessness from positive density;
- `cyclicIndex`, cyclic windows, and arbitrary-rank `CyclicBasisOrder`;
- contraction rank bookkeeping and basis lifting;
- abstract restriction/contraction gluing;
- balanced integer interleaving and periodic rational interleaving;
- `SolvesDivisibleKUMAtRank`, `SolvesKUMAtRankSize`, `SolvesKUMAtRank`, and lower-rank solver interfaces;
- generic divisible proper-tight reduction;
- generic rational proper-tight reduction.

The rational layer was added without replacing the older divisible interface. In reduced density ratio `p/q`, tight-set ranks factor by `q`, and the periodic scheduler glues restriction/contraction cyclic orders at the original density.

## Low-rank bases

- Rank 1 divisible KUM: **formalized internally**.
- Rank 2 divisible KUM: **formalized internally** through the native HalfWeave-style implementation.
- Rank 3 divisible KUM: **formalized internally through a frozen vendored proof**. `vendor/Rank3KUM/` is a source snapshot of Rank3KUM version-3 commit `eff642a2e01fac4fc1f6f76e592eeea46c3152c9`. It is exact apart from the toolchain patches listed in `vendor/Rank3KUM/PATCHES.md`; `HigherRankKUM/LowRank/RankThree.lean` is the narrow adapter into the generic solver interface.

HigherRankKUM does **not** currently contain a full formal proof of arbitrary-size rank-two KUM or a formalization of the van den Heuvel–Thomassé coprime theorem. Odd-size rank-two instances may therefore appear as explicit hypotheses even when they are settled mathematically in the literature.

No axiom or live external Rank3KUM dependency is used.

## Rank 4 — proper-tight branches

### Divisible size `|E|=4k`

All positive lower divisible ranks are internally available, so

`exists_cyclicBasisOrder_of_rank_four_of_nonempty_proper_tight`

is an unconditional internal theorem for finite uniformly dense rank-four matroids on `4k` elements with a nonempty proper tight set.

### Gcd-two size `|E|=4k+2`

Sprint 1 proves the rational reduction

`exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight`.

This is **formalized conditional** on

`SolvesKUMAtRankSize α 2 (2*k+1)`.

The remaining rank-two instance has odd ground-set size and is settled mathematically by the coprime theorem, but that external theorem is not silently imported into Lean.

Thus the genuinely new rank-four structural work is concentrated in the **strictly uniformly dense** branches.

## Strict gcd-two rank four — pair-cycle route

Sprints 2–3 formalize a conditional structural route for `|E|=4k+2`. Starting from an admissible pair cycle, the repository now proves:

- local shifted-window compatibility has full Boolean support;
- fixed-cycle nonorientability is exactly a forced functional transition with odd/no-fixed-point composition around the successor orbit;
- an admissibility-preserving local `2+2` repartition is controlled by two rank-two boundary contractions;
- the local operation is a common-base problem between a left boundary matroid and the dual of a right boundary matroid;
- uniqueness of the current local common base forces a loop on one boundary side;
- that loop translates to an ambient closure incidence in the original matroid;
- in rank four, `unique_adjacent_repartition_forces_neighbor_closure` packages the four possible neighboring closure obstructions;
- `exists_alternative_repartition_of_neighbor_closure_free` gives the useful contrapositive: a boundary with none of those closure incidences has another valid local repartition.

These results use no simplicity or representability hypothesis. They also do **not** establish that every strict gcd-two matroid admits an admissible pair cycle, that the re-pairing graph is connected, or that a sequence of local repairs always reaches an orientable cycle.

## Exact finite evidence

The trusted repository preserves reproducible certificates for:

- a strict 10-element binary rank-four fixed-pair obstruction for which another admissible pair cycle gives an explicit CBO;
- one strict 18-element binary rank-four obstruction whose 30,720-vertex admissible adjacent-exchange component has maximum distance two to orientability;
- a normalized four-block `GF(2)^4` local audit showing that the closure obstruction may occur only on the left, only on the right, or on both sides.

The local audit is an anti-overgeneralization guardrail: the disjunctive closure theorem should not be strengthened to require both sides. Likewise, closure-freeness guarantees an alternative full `2+2` repartition but not necessarily a single-element cross exchange.

All of these are **computational evidence** scoped to the certified finite objects, not KUM proofs.

## Strict divisible rank four

For `|E|=4k` with no nonempty proper tight set, the main live route remains controlled deletion/reinsertion. Matroid partition already gives existence of a basis decomposition in the integral-density setting; the unresolved issue is the additional control needed to delete and reinsert without losing the cyclic-basis condition.

Rank3KUM's strict-density, two-gap, splicing, near-tight, and six-point arguments remain sources of proof patterns only. They are not mechanically generalized here.

## Research frontier

The immediate mathematical fronts are:

1. **strict gcd-two:** prove existence of a useful admissible pair-cycle representation or replace it by a broader always-available structure;
2. **strict gcd-two:** understand how the new neighbor-closure obstructions can accumulate, and whether strict density forces an escape from locally rigid configurations;
3. **strict divisible:** formulate controlled basis deletion/reinsertion via exchange support, matching, or a suitable higher-rank gap condition;
4. formalize external coprime infrastructure only when it materially shortens the remaining internal dependency boundary.

See `docs/RANK4_COVERAGE.md`, `docs/research-ledger/SPRINT1.md`, `docs/research-ledger/SPRINT2.md`, and `docs/research-ledger/SPRINT3.md`.
