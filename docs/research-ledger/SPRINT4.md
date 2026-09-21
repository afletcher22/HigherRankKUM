# Sprint 4 — global closure geometry after local repair

**Start date:** 2026-09-15 (America/Phoenix)

**Branch:** `rank4-research-sprint4`

**Base checkpoint:** `checkpoint/sprint3-gcd-two-local-repair`

**Base SHA:** `b4ffc82e8b7d6d02a39e7f4b3d8cdfd7e894f08e`

**Base validation:** GitHub Actions run `35042601035` green, including all committed finite certificates, the targeted pair-cycle/local-repair Lean stack, and full `lake build`.

## Bounded question

Study the global geometry forced by repeated rank-four neighbor-closure obstructions in the strict `gcd(|E|,4)=2` branch.

Sprint 3 proved a local statement: if an adjacent `2+2` repair is unique, one of four neighboring ambient closure incidences must occur. Equivalently, if all four such incidences are absent, some alternative common-base repartition exists.

Sprint 4 asks how these local repairs interact around an odd admissible pair cycle. The current goal is **not** to prove pair-cycle existence. Instead, conditional on an admissible pair cycle, identify dynamics that force eventual fixed-cycle orientability.

Keep four questions separate:

1. fixed-cycle relation orientability;
2. existence of alternative admissible repartitions;
3. reachability of an orientable admissible pair cycle;
4. existence of an admissible pair cycle in the first place.

## Abstract four-element guardrail

`experiments/sprint4_abstract_repartition_guardrail.py` enumerates all rank-two matroids on a labelled four-element ground and all ordered pairs `(L,S)` of such boundary matroids.

Fix `B={0,1}` and `D={2,3}`. Among configurations where `B` is a common base, neither element of `D` is a loop of `L`, and neither element of `B` is a coloop of `S`:

- 36 rank-two matroids occur;
- 1,296 ordered boundary pairs are checked;
- 100 satisfy the closure-free surrogate;
- none has `B` as unique common base;
- 98 have a one-element cross common base;
- exactly 2 do not: the only alternative is the wholesale opposite block `D`;
- common-base count histogram: `2:22`, `3:28`, `4:34`, `5:15`, `6:1`.

The exceptional swapped pair has base families

- `{01,03,12,23}`;
- `{01,02,13,23}`.

**Guardrail:** do not replace “an alternative local `2+2` repartition exists” by “a one-element cross exchange exists.” The latter is false under the abstract hypotheses currently formalized.

## Candidate closure potential

For pair blocks `B_i`, define

`Phi = sum_i (|B_(i+1) ∩ cl(B_(i-1))| + |B_i ∩ cl(B_(i+2))|)`.

After cyclic reindexing this is the symmetric sum over distance-two block pairs. It is built from the exact neighbor-closure incidences appearing in Sprint 3 local rigidity.

### Preserved 10-element witness

Across all 576 admissible pair cycles:

- 8 are unorientable, 568 orientable;
- all 8 unorientable cycles have `Phi=4`;
- orientable histogram: `4:40`, `5:208`, `6:272`, `7:48`;
- every unorientable cycle has a legal full `2+2` repartition with strictly larger `Phi`;
- every unorientable cycle reaches an orientable cycle in one strictly score-increasing repair.

`Phi` is not an orientability classifier because 40 orientable states also have score 4.

### Preserved 18-element witness

Across the exact 30,720-vertex component:

- 7,680 unorientable states, with `Phi=18:3072`, `Phi=20:4608`;
- 23,040 orientable states, with `Phi=21:9216`, `22:4608`, `23:9216`;
- every unorientable state is closure-saturated at all 9 local boundaries;
- every unorientable state has a legal full `2+2` repair that strictly increases `Phi`;
- 6,912 reach orientable in one strictly increasing repair;
- 768 need two strictly increasing repairs.

This remains witness-specific.

## Exhaustive normalized binary `N=5`

`experiments/sprint4_n5_binary_closure_potential_exhaustive.py` exhausts normalized admissible pair cycles over `GF(2)^4`, fixing

- `B_0=(1,2)`;
- `B_1=(4,8)`.

Exact result:

- 49,896 normalized admissible configurations;
- 43,546 strictly uniformly dense;
- exactly 80 unorientable in total;
- all 80 are strictly uniformly dense;
- closure scores: `Phi=2:40`, `Phi=4:40`;
- all 80 have a legal full `2+2` repair that both strictly increases `Phi` and is already orientable;
- maximum gain: `+1` in 40 cases, `+2` in 40 cases;
- distance-two closure-edge patterns, modulo dihedral symmetry:
  - `(0,0,0,0,2)` — 40;
  - `(0,0,0,2,2)` — 40.

This is exact only for represented binary `N=5`.

## Binary `N=7` plateau falsification

The universal statement

> every non-orientable admissible pair cycle has a strictly `Phi`-increasing legal repair

is **false**.

`experiments/sprint4_n7_binary_phi_plateau_certificate.py` gives an exact fixed binary `N=7` regression witness:

`((1,2),(4,8),(13,14),(4,8),(13,14),(5,9),(7,8))`.

Certified properties:

- every adjacent block union is a basis;
- the represented rank-four matroid on 14 labelled elements is strictly uniformly dense;
- maximum flat occupancies are rank 1: `3`, rank 2: `6`, rank 3: `10`, exactly below the strict-density thresholds;
- forced relation bits are `(0,0,0,1,1,1,0)`, hence the state is unorientable;
- distance-two closure-edge scores are `(0,4,4,0,0,0,2)`;
- `Phi=10`;
- all 12 legal local-repartition occurrences are exhausted, with 6 distinct targets;
- gain histogram is `0:9`, `-1:2`, `-2:1`;
- **no legal repair increases `Phi`**;
- nevertheless a legal equal-`Phi` repair is already orientable.

One explicit equal-score orientable target, repairing boundary 6, is

`((1,7),(4,8),(13,14),(4,8),(13,14),(5,9),(2,8))`.

This counterexample is a permanent guardrail against restoring unconditional strict ascent as the target theorem.

### Exploratory larger-odd-`N` checks

Uncommitted randomized binary falsification searches support the refined dynamics statement:

- among 1,000 sampled strict unorientable `N=7` states, 978 had both strict ascent and a direct orientable repair; 22 were `Phi` plateaus, and all 22 had a direct orientable repair;
- among 52 sampled strict unorientable `N=9` states, 49 had strict ascent and a direct orientable repair; 3 were plateaus, all with direct orientable repair;
- among 14 sampled strict unorientable `N=11` states, 12 had strict ascent and a direct orientable repair; 2 were plateaus, both with direct orientable repair.

These samples are search guidance only, not certificates.

## Formal infrastructure

### Generic potential theorems

`HigherRankKUM/PotentialAscent.lean` contains:

- `exists_reachable_good_of_bounded_strict_ascent`;
- `good_of_no_strict_ascent`.

After the `N=7` falsification it also contains the weaker generic principle:

- `exists_reachable_good_of_bounded_escape_or_strict_ascent`;
- `good_or_exists_good_move_of_no_strict_ascent`.

The refined principle allows a non-good state either to move directly to a good state or, if it continues, to move with strictly larger bounded potential.

### Rank-four closure potential

`HigherRankKUM/Rank4/GcdTwoClosurePotential.lean` formalizes:

- `closureIndicator`;
- `boundaryClosureScore A s`;
- `closurePotential A`;
- `boundaryClosureScore_le_four`;
- `closurePotential_le_four_mul`: `closurePotential A ≤ 4N`;
- `boundaryClosureScore_pos_of_unique`;
- `card_le_closurePotential_of_all_unique`;
- `exists_alternative_repartition_of_closurePotential_lt_card`.

The last theorem is representation-free but only guarantees an alternative common-base repartition when `Phi < N`; it does not control the new score or orientability.

## Repaired-state constructor — validated checkpoint

The former proof-engineering gap

`common base Q -> new AdmissiblePairCycle.Data`

is now closed.

New reusable layers:

- `HigherRankKUM/PairBlockPartition.lean` — abstract partition of the ground into 2-element blocks and reconstruction of a global `Fin N × Bool ≃ M.E`;
- `HigherRankKUM/PairBlockPartitionReplace.lean` — replacing two blocks by any disjoint two-element pair with the same four-element union preserves the pair partition;
- `HigherRankKUM/Rank4/GcdTwoRepairTransition.lean` — a `LocalRepartition` gives a new global pair equivalence with exact changed/unchanged pair-set theorems;
- `HigherRankKUM/Rank4/GcdTwoRepairAdmissible.lean` — the replacement preserves all aligned rank-four basis windows, producing a new `AdmissiblePairCycle.Data`.

**Validated source checkpoint:** `a9479db5cc563a30913686cdf63d92456c0a6a4f`.

**Validation:** GitHub Actions run `35087640770` fully green, including targeted Lean stack, all finite certificates, and full `lake build`.

This closes the state-transition engineering bottleneck. A common-base repair is no longer merely a local set witness; it can be iterated as an actual admissible pair-cycle state transition.

## Repair graph and corrected dynamics reduction

`HigherRankKUM/Rank4/GcdTwoRepairMove.lean` adds:

- `commonBaseRepairTarget`;
- `RepairMove` — one legal local repartition followed by the repaired admissible-state constructor;
- `repairMove_commonBaseRepairTarget`;
- `RelationOrientable` — fixed pair-cycle Boolean-relation orientability;
- `exists_reachable_relationOrientable_of_strict_closure_ascent` — retained as a strong conditional theorem, but its universal hypothesis is now known false;
- `exists_reachable_relationOrientable_of_escape_or_strict_closure_ascent` — the corrected reduction;
- the corresponding local-maximum escape theorem.

The corrected hard hypothesis is:

> for every non-orientable admissible pair-cycle state, either some one-step `RepairMove` is relation-orientable, or some `RepairMove` strictly increases `closurePotential`.

Because `closurePotential ≤ 4N`, that disjunction is sufficient for finite reachability of an orientable admissible state.

**Current combined source head:** `a5498fa0073d35d801ebea0fb196811cd2110f6a`.

**Current validation run:** `35143111762` pending at the time of this ledger update. Do not treat this combined dynamics head as fully green until that run completes.

## Refined mathematical target

The next theorem should no longer attempt unconditional ascent. A more promising proof decomposition is:

1. assume `A` is not `RelationOrientable` in the intended odd-`N` gcd-two regime;
2. use the Sprint 2 obstruction theorem to conclude that every local Boolean relation is a forced bijection and the total successor composition is fixed-point-free;
3. choose a legal alternative common-base repair using the Sprint 3/Sprint 4 rank-two boundary geometry;
4. inspect the repaired state:
   - if an affected local relation gains Boolean slack, use `admissible_pair_cycle_orientable_of_local_slack` to obtain the **escape** branch;
   - if all affected local relations remain forced bijections, prove that the repair can be chosen so that `closurePotential` strictly increases.

This is materially sharper than the old target. The potential only needs to be monotone on repairs that **remain inside the forced non-orientable region**.

The key local research question is therefore:

> What closure/rank-two-flat constraints are forced when both the old state and a legal repaired state retain functional full-support Boolean relations at every affected index?

A theorem answering that may convert “no local slack after repair” directly into strict closure gain.

## Additional structural targets

### Closure-saturation bookkeeping

Classify cyclic patterns of the four neighbor-closure incidences under strict uniform density. The binary `N=5` obstruction patterns provide the smallest exact test cases, while the `N=7` plateau shows that high closure score alone does not force ascent.

### Propagation through rank-two flats

Because each rank-four core is one pair block, repeated closure incidences constrain neighboring blocks inside rank-two flats. Search for statements such as:

- repeated one-sided closure forces a larger low-rank flat;
- alternating closure directions force periodicity;
- persistence of forced Boolean bijections across a repair forces one of the affected distance-two closure contributions to increase.

### Orientability bridge

`RelationOrientable` is deliberately only the fixed pair-cycle relation notion. Keep the later theorem converting an orientable admissible pair cycle into the desired cyclic basis ordering explicit and separate.

## Non-goals / guardrails

- no claim that rank-four KUM is solved;
- no claim that every strict gcd-two rank-four matroid admits an admissible pair cycle;
- no assumption that the repair graph is connected;
- no universal one- or two-step repair theorem inferred from finite witnesses;
- no universal strict-`Phi`-ascent claim — explicitly falsified by the certified binary `N=7` plateau;
- no cross-exchange theorem without additional hypotheses;
- no representability assumption in abstract statements unless explicit;
- no broad random search substituted for structural proof.

## Sprint success criterion

Produce a reusable structural lemma about repairs that **remain non-orientable**, ideally proving a strict increase in closure geometry under the no-slack hypothesis; or find and certify a counterexample that forces a further refinement. The proof-engineering side is now sufficiently complete that future mathematical repair lemmas can be expressed directly as state transitions.
