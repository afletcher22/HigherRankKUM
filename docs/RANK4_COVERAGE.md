# Rank-Four KUM Coverage Map

This document separates arithmetic regimes before structural case splitting. That distinction is essential in rank four.

Let `n = |E(M)|` and `r(M)=4`.

## Arithmetic split

### 1. Coprime regime

`gcd(n,4)=1`, equivalently `n` is odd.

This is settled mathematically by the van den Heuvel–Thomassé coprime theorem. HigherRankKUM does not currently formalize that external theorem.

### 2. Intermediate gcd-two regime

`gcd(n,4)=2`, equivalently `n = 4k+2`.

Sprint 1 added the rational-density/full-rank interface needed to treat proper tight sets in this regime. The theorem

`exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight`

is Lean verified conditional on the exact odd-size rank-two solver

`SolvesKUMAtRankSize α 2 (2*k+1)`.

Mathematically that rank-two instance is supplied by the coprime theorem because `2*k+1` is odd; it is deliberately not imported as a Lean axiom. Thus the proper-tight gcd-two branch is reduced formally and settled mathematically modulo the cited external theorem.

The remaining gcd-two research frontier is the **strictly uniformly dense** branch. Sprints 2–3 develop one structural route for it based on admissible pair cycles, orientation obstructions, and local re-pairing.

Important scope boundary: the current pair-cycle machinery assumes an `AdmissiblePairCycle.Data`. It does **not** prove that every strict gcd-two rank-four matroid admits such a pair cycle, nor that every re-pairing path reaches an orientable cycle.

### 3. Divisible regime

`4 | n`, so `n=4k`.

This is the regime addressed by the original divisible tight-set induction machinery.

## Structural split inside the divisible regime

Assume `n=4k` and uniform density with parameter `k`.

### Nonempty proper tight set — formalized

Ranks 1, 2, and 3 in the divisible solver hierarchy are available internally. Therefore

`exists_cyclicBasisOrder_of_rank_four_of_nonempty_proper_tight`

is an unconditional internal theorem: every finite uniformly dense rank-four matroid on `4k` elements with a nonempty proper tight set has a cyclic basis ordering.

The possible proper-tight ranks `1,2,3` correspond conceptually to `1+3`, `2+2`, and `3+1`; the production proof handles them uniformly through the lower-rank reduction.

### No nonempty proper tight set — open

This is the strictly uniformly dense divisible rank-four branch. The current live route is controlled deletion/reinsertion rather than merely proving that some basis can be deleted.

## Strict gcd-two pair-cycle progress

For a rank-four admissible pair cycle on `2N=4k+2` elements (`N` odd), HigherRankKUM now contains:

- an exact Boolean-relation characterization of fixed-cycle orientation failure;
- the contraction interpretation of each local compatibility relation;
- the two-boundary criterion for an admissibility-preserving local `2+2` repartition;
- a four-element common-base rigidity theorem;
- an ambient closure bridge from local loops to closure in the original matroid;
- the rank-four theorem `unique_adjacent_repartition_forces_neighbor_closure`;
- the operational contrapositive `exists_alternative_repartition_of_neighbor_closure_free`.

The last theorem says that if none of the four neighboring closure incidences occurs, the current `2+2` split is not the unique local common base. It intentionally allows a wholesale swap of the two blocks; closure-freeness alone does not force a one-element cross exchange.

Exact finite certificates currently include a strict 10-element binary fixed-cycle obstruction and a strict 18-element binary obstruction component. Both concern actual labelled binary matroids, not abstract relation patterns. They refute naive fixed-cycle / one-break strengthenings but do not refute KUM.

## Current schematic coverage

```text
Rank-4 KUM
│
├── gcd(n,4)=1
│   └── SOLVED mathematically by coprime theorem
│
├── gcd(n,4)=2   [n=4k+2]
│   │
│   ├── nonempty proper tight set
│   │   └── reduced in Lean to odd-size rank-2 KUM;
│   │       mathematically discharged by coprime theorem
│   │
│   └── no nonempty proper tight set
│       └── OPEN
│           ├── admissible-pair existence not yet universal
│           └── pair orientation / local repair machinery formalized conditionally
│
└── gcd(n,4)=4   [n=4k]
    │
    ├── nonempty proper tight set
    │   └── SOLVED / FORMALIZED internally
    │
    └── no nonempty proper tight set
        └── OPEN: strict divisible deletion/reinsertion frontier
```

## Immediate research milestones

1. For strict gcd-two rank four, determine what guarantees a useful admissible pair cycle, or identify a broader representation that is always available.
2. Use the new closure obstruction to study whether locally rigid boundaries can accumulate without violating strict density.
3. Separate full local `2+2` repartitions from the stronger single-element cross-exchange operation; do not silently identify them.
4. In the divisible strict branch, pursue controlled deletion/reinsertion and exchange-support formulations independently of the gcd-two pair-cycle route.
5. Keep computational evidence scoped to the exact matroids/components certified; promote only stable structural statements into the Lean tree.

See `docs/GENERALIZATION_STATUS.md`, `docs/research-ledger/SPRINT1.md`, `docs/research-ledger/SPRINT2.md`, and `docs/research-ledger/SPRINT3.md`.
