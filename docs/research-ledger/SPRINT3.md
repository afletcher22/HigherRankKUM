# Sprint 3 — adjacent re-pairing component audit

**Start date:** 2026-09-15 (America/Phoenix)

**Branch:** `rank4-research-sprint3`

**Base ledger commit:** `d70b3040ff57758e6c682ef10756782747de3f4e`

**Validated Sprint 2 source:** `02dfac3ffad863a6a09570b7e077a93541654f0d` (full CI run `35008387570` green).

## Bounded question

Take one preserved 18-element binary rank-four obstruction from the historical `m=9` search and audit it under the narrower operation of admissibility-preserving exchange of one labelled element between adjacent pair blocks.

This sprint does **not** search all rank-four matroids and does not propose a universal one- or two-step repair theorem.

## Preserved witness

Pair vector values over `GF(2)^4`:

`(1,2), (4,8), (1,6), (2,8), (1,4), (2,12), (1,8), (2,4), (5,8)`.

The labelled ground elements are positions `0,...,17`; repeated vector values are distinct parallel elements.

## Independent audit performed before commit

- ambient rank: 4;
- all 9 adjacent pair unions are bases;
- local relations: eight equalities and one inequality, hence odd forced parity;
- all 512 orientations of the starting pair cycle fail;
- all 262,142 nonempty proper subsets satisfy strict density `2|A| < 9 r(A)`;
- all 27,648 orders in the historical one-break class fail;
- the full connected component under admissibility-preserving adjacent element exchange has 30,720 vertices and 149,760 directed edges;
- 23,040 component vertices are orientable and 7,680 are unorientable;
- among unorientable vertices, 6,912 have distance 1 to orientability and 768 have distance 2;
- the starting historical obstruction has distance exactly 2;
- maximum distance to an orientable vertex in this component is 2.

One shortest repaired pair cycle is reached by two adjacent exchanges and admits the CBO label order

`5,0,3,1,2,4,7,6,9,8,11,10,13,12,15,14,17,16`.

## Interpretation

The historical fact that this witness resists every one-break repair does not imply that it is trapped under successive admissibility-preserving re-pairings. In this component, two local re-pairings suffice.

This is exact finite computational evidence about one labelled binary matroid only. It does not imply that every obstruction has distance at most two, that every admissible-pair graph is connected, or that every strict gcd-two matroid has a favorable admissible pair cycle.

## Single next task

Preserve a deterministic verifier and its expected result for this component. Then extract the local structural condition governing an admissibility-preserving adjacent exchange: only the two boundary aligned windows can change, so the move should be expressible as a common-basis condition on the four involved elements after contracting the unchanged interior. Formalize that local move criterion before any broader computation.
