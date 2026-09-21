# Sprint 3 — adjacent re-pairing and local rigidity

**Start date:** 2026-09-15 (America/Phoenix)

**Branch:** `rank4-research-sprint3`

**Base ledger commit:** `d70b3040ff57758e6c682ef10756782747de3f4e`

**Validated Sprint 2 source:** `02dfac3ffad863a6a09570b7e077a93541654f0d` (full CI run `35008387570` green).

**Closeout rule:** freeze an immutable Sprint 3 checkpoint only after the final branch head passes the certificate suite, targeted repair build, and full `lake build`.

## Bounded question

Start from a preserved 18-element binary rank-four fixed-pair obstruction and determine whether admissibility-preserving local re-pairing escapes it. Then extract the matroid structure controlling a single local `2+2` repartition.

This sprint does **not** search all rank-four matroids and does not claim a universal one- or two-step repair theorem.

## Exact 18-element certificate

Preserved pair vector values over `GF(2)^4`:

`(1,2), (4,8), (1,6), (2,8), (1,4), (2,12), (1,8), (2,4), (5,8)`.

The labelled ground elements are positions `0,...,17`; repeated vector values are distinct parallel elements.

The deterministic verifier certifies:

- ambient rank 4;
- all 9 adjacent pair unions are bases;
- all 512 orientations of the starting pair cycle fail;
- all 262,142 nonempty proper subsets satisfy strict density `2|A| < 9 r(A)`;
- all 27,648 orders in the historical one-break class fail;
- the connected component under admissibility-preserving adjacent element exchange has 30,720 vertices and 149,760 directed edges;
- 23,040 component vertices are orientable and 7,680 are unorientable;
- among unorientable vertices, 6,912 have distance 1 to orientability and 768 have distance 2;
- the starting historical obstruction has distance exactly 2;
- maximum distance to an orientable vertex in this component is 2;
- every unorientable vertex has exactly three rigid boundaries under the full six-choice local `2+2` repartition audit;
- the rigid-boundary gap patterns are `(1,3,5)`, `(1,1,7)`, and `(3,3,3)`, with the 768 distance-two states exactly the `(3,3,3)` class in this witness.

One shortest repaired pair cycle is reached by two adjacent exchanges and admits the CBO label order

`5,0,3,1,2,4,7,6,9,8,11,10,13,12,15,14,17,16`.

These are exact finite facts about one labelled binary matroid only.

## Formal local-repair structure

### Two-boundary criterion

`AdjacentRepair.admissible_two_boundary_repair_iff_contract_bases` formalizes the general observation that changing two adjacent pair blocks can affect only the two boundary aligned windows. After contracting their unchanged interiors, the move is controlled by two rank-two boundary matroids.

The complementary right pair can be dualized, so a proposed left pair is valid exactly when it is a common base of the left boundary matroid and the dual of the right boundary matroid.

### Four-element rigidity

`LocalRepairRigidity.unique_common_pair_base_forces_loop_or_coloop` proves, without simplicity or representability, that if the current pair is the unique common base on the four-element local ground, then an opposite-side element is a loop on the left or a current-side element is a coloop on the dual-right side.

`LocalRepairBoundary.unique_common_pair_with_dual_forces_boundary_loop` converts the dual coloop alternatives into loops on the original right boundary matroid.

### Ambient closure bridge

`LocalRepairClosure.mem_closure_of_boundaryMinor_isLoop` translates a loop in a restricted contraction back into membership in the ambient closure of the contracted core.

`LocalRepairClosure.unique_local_repair_forces_ambient_closure` combines the local rigidity theorem with that bridge.

### Rank-four specialization

For rank four (`h=2`), each unchanged core is exactly one pair block. `Rank4GcdTwoRepair` packages the cyclic-index geometry and proves

`unique_adjacent_repartition_forces_neighbor_closure`:

if the current adjacent `2+2` repartition is the unique common base of the two local boundary matroids, then at least one moved element lies in the ambient closure of the neighboring unchanged pair on the left or right.

The operational contrapositive

`exists_alternative_repartition_of_neighbor_closure_free`

states that if none of the four possible neighbor-closure incidences occurs, there is another common-base `2+2` repartition.

The conclusion intentionally permits the wholesale swap of the two current blocks. Closure-freeness alone does not imply the stronger existence of a single-element cross exchange.

## Anti-overgeneralization certificate

`experiments/sprint3_local_rigidity_sanity.py` exhaustively audits a normalized four-block `GF(2)^4` local model. Among 256 forced-neighbor local configurations, rigid examples occur with closure on only the left, only the right, or both sides.

This protects the formal theorem's disjunctive conclusion: neither a two-sided closure conclusion nor a forced cross-exchange conclusion is justified by the current hypotheses.

## Interpretation

Sprint 3 changes the status of the pair-cycle route from a finite repair observation to a structural theorem:

> local inability to repartition is witnessed by ambient rank-two closure geometry.

That is a useful obstruction, not yet a global solution. Three gaps remain before it could settle strict gcd-two rank four:

1. existence of a useful admissible pair-cycle representation for an arbitrary strict gcd-two matroid;
2. a global argument controlling how the neighbor-closure obstructions can accumulate;
3. a termination or potential argument showing that allowed re-pairings can reach Boolean slack / orientability rather than cycle indefinitely.

## Sprint closeout

**Lean verified on the targeted repair stack:** the two-boundary contraction criterion; common-base/dual packaging; four-element loop-or-coloop rigidity; boundary-loop and ambient-closure bridges; rank-four cyclic specialization; closure-free alternative-repartition corollary once the final head passes CI.

**Computationally certified:** the strict 10-element repair witness inherited from Sprint 2; the full 30,720-vertex 18-element component audit; the four-block local rigidity sanity audit.

**Refuted / guarded against:** universal fixed-pair orientability; universal one-break sufficiency on the preserved 18-element witness; strengthening local rigidity to require closure on both sides; silently replacing full `2+2` repartition by single-element exchange.

**Still unsupported:** universal admissible-pair existence; universal connectivity of the local-repartition graph; a bounded repair theorem for all strict gcd-two rank-four matroids; any claim that rank-four KUM is solved.

**Single next task:** study the global geometry forced by repeated rank-four neighbor-closure obstructions. In parallel, preserve the abstract four-element guardrail distinguishing an arbitrary alternative `2+2` repartition from a genuine cross exchange. Do not begin a broad rank-four search until that structural question is sharper.
