# Sol handoff — HigherRankKUM Sprint 3 closeout

This file records the certified Sprint 3 state and the exact starting point for Sprint 4.

## Frozen checkpoint

- repository: `afletcher22/HigherRankKUM`
- immutable branch: `checkpoint/sprint3-gcd-two-local-repair`
- exact SHA: `b4ffc82e8b7d6d02a39e7f4b3d8cdfd7e894f08e`
- validation PR: `#12` (closed, intentionally not merged)
- final validation run: `35042601035`
- validation status: green

The final run passed:

- dependency-lock verification;
- vendored Rank3KUM integrity verification;
- standalone Rank3KUM import-boundary enforcement;
- Sprint 2 obstruction certificate;
- 10-element adjacent-repair certificate;
- 18-element repair-component certificate;
- local repair rigidity sanity certificate;
- targeted pair-cycle/local-repair Lean build, including the rank-four geometry and corollary modules;
- full repository `lake build`.

## Sprint 3 mathematical advance

Sprint 2 had isolated the fixed admissible pair-cycle obstruction in the rank-four `gcd(|E|,4)=2` regime: cyclic unsatisfiability is exactly the forced-bijection / no-fixed-point Boolean obstruction for the local orientation relations.

Sprint 3 moved from that fixed-cycle obstruction to the geometry of changing adjacent pair blocks.

### Two-boundary repair criterion

`HigherRankKUM/AdjacentRepair.lean`

The theorem

`AdjacentRepair.admissible_two_boundary_repair_iff_contract_bases`

shows that replacing two adjacent pair blocks affects only two aligned basis windows. After contracting the unchanged cores, legality of the repair is controlled by two rank-two boundary matroids.

This packages a local `2+2` repartition as a common-base question between a left boundary matroid and the dual of a right boundary matroid.

### Four-element rigidity

`HigherRankKUM/LocalRepairRigidity.lean`

`LocalRepairRigidity.unique_common_pair_base_forces_loop_or_coloop`

proves the exact four-element statement: if the current pair is the unique common base of two rank-two matroids on a four-element ground, then either an opposite element is a loop in the left matroid or a current-pair element is a coloop in the other matroid.

No simplicity or representability hypothesis is used.

### Boundary and ambient closure bridge

`HigherRankKUM/LocalRepairBoundary.lean`

`LocalRepairBoundary.unique_common_pair_with_dual_forces_boundary_loop`

converts the dual-right coloop alternative into a loop in the original right boundary matroid.

`HigherRankKUM/LocalRepairClosure.lean`

`LocalRepairClosure.mem_closure_of_boundaryMinor_isLoop`

translates a loop of the restricted contraction back into ambient closure of the contracted core.

`LocalRepairClosure.unique_local_repair_forces_ambient_closure`

combines the local rigidity theorem with this bridge.

### Rank-four cyclic specialization

`HigherRankKUM/Rank4/GcdTwoRepairGeometry.lean`

`Rank4GcdTwoRepair.unique_adjacent_repartition_forces_neighbor_closure`

specializes the machinery to `h=2`: if the current adjacent `2+2` repartition is unique, then at least one of four neighboring ambient closure incidences must hold.

`HigherRankKUM/Rank4/GcdTwoRepairCorollary.lean`

`Rank4GcdTwoRepair.exists_alternative_repartition_of_neighbor_closure_free`

is the operational contrapositive: if all four neighbor-closure incidences are absent, there exists another common-base `2+2` repartition distinct from the current pair.

Important: the conclusion deliberately allows the wholesale exchange of the two blocks. It does **not** assert the existence of a one-element cross exchange.

The root `HigherRankKUM.lean` exports this rank-four repair stack.

## Exact finite evidence preserved

### 10-element strict binary witness

For the preserved strict rank-four binary matroid on 10 labelled elements, the initially chosen admissible pair cycle has all 32 orientations failing. Exhaustive enumeration of all 22,680 cyclic pair decompositions found 576 admissible pair cycles, only 8 unorientable. All 8 admit an admissibility-preserving adjacent repair to an orientable cycle; the admissible-cycle graph is connected for this witness.

This refutes any inference that fixed-cycle failure is a KUM failure.

### 18-element strict binary witness

The preserved vector sequence is

`(1,2,4,8,1,6,2,8,1,4,2,12,1,8,2,4,5,8)`.

Exact component audit under admissibility-preserving adjacent exchanges:

- 30,720 vertices;
- 149,760 directed admissible moves;
- 23,040 orientable vertices;
- 7,680 unorientable vertices;
- 6,912 unorientable vertices at distance 1 from orientability;
- 768 at distance 2;
- maximum distance to orientability in this component is 2;
- every unorientable vertex has exactly three rigid boundaries under the full local six-choice `2+2` repartition audit;
- rigid-gap patterns are `(1,3,5)`, `(1,1,7)`, and `(3,3,3)` for this witness.

The historical starting obstruction has distance 2.

These facts are witness-specific and are not universal repair theorems.

### Local rigidity sanity certificate

`experiments/sprint3_local_rigidity_sanity.py`

The normalized `GF(2)^4` local audit checks 256 forced-neighbor configurations. Rigid examples can have closure only on the left, only on the right, or on both sides. This is retained specifically to prevent strengthening the formal disjunction beyond what the theorem proves.

## CI failure and repair history

The first validation run on Sprint 3 failed only in `HigherRankKUM.Rank4.GcdTwoRepairGeometry`.

Cause: rewriting with `Matroid.isBase_restrict_iff` inferred the restriction ground as the explicit union of the two local blocks, while the theorem target used the definition `repairGround A s`. The expressions were propositionally equal but not syntactically aligned for the rewrite.

Fix: introduce an exactly typed hypothesis

```lean
have hrepairGround : repairGround A s ⊆ (M.contract ...).E := by
  simpa [repairGround, i, j] using Set.union_subset hiGround hjGround
```

then rewrite with

```lean
rw [leftRepairMinor, LocalRepairClosure.boundaryMinor,
  Matroid.isBase_restrict_iff hrepairGround]
apply hcontract.isBasis_of_subset (hX := hrepairGround)
simp [repairGround, i, j]
```

and analogously on the right.

The fix commit was `b9787791969810c0fba41260aede15e3aea9e5f3`.

Subsequent targeted compilation passed, and final run `35042601035` passed the full build.

## Sprint 3 closeout commits of note

- `b9787791969810c0fba41260aede15e3aea9e5f3` — fix restriction-basis proof alignment;
- `4b9aed95cb266e08eef75da39f5f3628b3feb9d7` — add closure-free alternative-repartition theorem;
- `27c6f06ff5236e4873bd334d48ca005c4558b211` — export rank-four repair stack;
- `686d923eeac85fdca849d890e6b6ef54a54dfe83` — strengthen CI for local rigidity and rank-four corollary;
- `824d39beeace93b13c2010a06cc2d58e5179f15c` — refresh rank-four coverage;
- `6a63ddbdf457d4dfcc592942bf63e205bc6e2d97` — refresh generalization status;
- `2d439a30e4a1b350c3b62e6b88c57a7df300f7ae` — align rank-four experiment tracks;
- `b4ffc82e8b7d6d02a39e7f4b3d8cdfd7e894f08e` — final Sprint 3 ledger closeout / frozen source SHA.

## Scope guardrails

The current work does **not** prove any of the following:

1. every strict rank-four gcd-two matroid has an admissible pair-cycle representation;
2. every admissible-pair-cycle repair graph is connected;
3. every unorientable admissible pair cycle is one or two repairs from an orientable one;
4. closure-free local geometry forces a one-element cross exchange;
5. rank-four KUM is solved.

The pair-cycle route remains conditional on having the pair-cycle data in hand. The existence problem is separate.

## Sprint 4 starting point

New branch: `rank4-research-sprint4`, based exactly on the frozen Sprint 3 checkpoint.

The bounded Sprint 4 target is global closure accumulation: understand what repeated instances of the Sprint 3 neighbor-closure obstruction can look like around an odd pair cycle, and whether strict uniform density forces a contradiction or supplies a monotone repair potential.

The first Sprint 4 guardrail exhaustively enumerates all 36 rank-two matroids on a labelled four-element ground and all 1,296 ordered boundary pairs. Among the 100 configurations satisfying the abstract closure-free surrogate with the current pair common:

- 0 have no alternative common base;
- 98 have a cross common base;
- exactly 2 have no cross common base and permit only the wholesale opposite-block swap.

The two exceptional ordered pairs are the swap of

- left bases `{01,03,12,23}`;
- dual-right bases `{01,02,13,23}`.

This is encoded in

- `experiments/sprint4_abstract_repartition_guardrail.py`;
- `experiments/sprint4_abstract_repartition_guardrail_result.json`;
- `docs/research-ledger/SPRINT4.md`.

The immediate mathematical task is therefore **not** to prove a cross-exchange theorem from the existing local hypotheses. It is to exploit additional global pair-cycle / strict-density structure to control closure-saturated boundaries or construct a termination potential for legal full `2+2` repartitions.
