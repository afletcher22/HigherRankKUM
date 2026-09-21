# Sprint 2 — gcd-two pair-orientation obstruction

**Start date:** 2026-09-15 (America/Phoenix)

**Branches:** `rank4-research-sprint2`, continued on `rank4-sprint2-fixes-repair`

**Base ledger commit:** `2507d1cd081b4291d36f545f04b215358677bbe4`

**Lean source inherited from Sprint 1:** `875d03def7517e80f764f5f327eea0eb5536c85a` (full `lake build` green, run `34946281862`).

## Sprint question

Characterize exactly when a fixed admissible gcd-two pair cycle cannot be oriented into a cyclic basis order, and verify that the recovered binary search evidence concerns realizable matroid pair cycles with the same notion of admissibility.

This sprint is **not** a proof of rank-four KUM or of the full gcd-two branch. Failure of one fixed pair cycle leaves open another circular representation, another pair cycle, or another non-pair-contiguous cyclic ordering.

## Bounded setup

Let `|E| = 2N`, `r(M) = 2h`, `gcd(N,h)=1`, and work in the nontrivial range `0 < h < N`.

An admissible pair cycle is a cyclic partition

`E = P_0 ⊔ ... ⊔ P_{N-1}`, `|P_i|=2`,

such that the union of every `h` consecutive pair blocks is a basis.

After orienting each pair, aligned rank-`2h` windows are bases by admissibility. The shifted window from block `i` is

`{last(P_i)} ∪ C_i ∪ {first(P_{i+h})}`,

where `C_i = P_{i+1} ∪ ... ∪ P_{i+h-1}`.

## Established structural result

### Abstract Boolean-relation theorem

For a cyclic list of Boolean relations with full support in both coordinates, cyclic unsatisfiability occurs iff every local relation is functional (hence, by full support on two states, a bijection) and the total relational composition has no fixed point.

Equivalently, the only obstruction is a forced transition at every local step whose total composition flips the initial Boolean state. In particular, if one local full-support relation is nonfunctional — equivalently it allows at least three of the four Boolean pairs — the cycle is satisfiable.

The argument is valid for lists of length two as well as longer cycles; it does not assume a simple graph with at least three vertices.

**Evidence:** Lean verified.

Main declarations:

- `BinaryRelationCycle.not_cyclicSatisfiable_iff`
- `BinaryRelationCycle.hasThreeAllowed_of_fullSupport_of_not_functional`
- `BinaryRelationCycle.bijectionRelation_of_not_hasThreeAllowed`
- `BinaryRelationCycle.forced_flip_of_no_fixed_point`
- `BinaryRelationCycle.composeList_is_flip_of_forced_no_fixed`

### Matroid-local theorem

For an exact admissible pair cycle and `0 < h < N`:

- the middle core `C_i` is independent;
- `|C_i| = 2h-2`;
- after contracting `C_i`, each endpoint pair is a basis of the rank-two contraction;
- the endpoint compatibility relation has full support;
- validity of the shifted rank-`2h` window is equivalent to membership in that local Boolean compatibility relation.

No simplicity or representability hypothesis is used.

**Evidence:** Lean verified.

Main declarations:

- `AdmissiblePairCycle.Data.core_indep`
- `AdmissiblePairCycle.Data.core_encard`
- `AdmissiblePairCycle.Data.endpoint_basis_left`
- `AdmissiblePairCycle.Data.endpoint_basis_right`
- `AdmissiblePairCycle.Data.localRelation_fullSupport`
- `AdmissiblePairCycle.Data.shifted_window_iff_localRelation`

### Successor-cycle characterization

When `gcd(N,h)=1`, multiplication by `h` modulo `N` enumerates every pair index exactly once. Therefore the fixed admissible pair cycle has an obstruction at the compatibility-relation level iff every local relation is a Boolean bijection and the composed transition around the single successor orbit has no fixed point.

Main declarations:

- `PairCycleObstruction.stepIndex_injective`
- `PairCycleObstruction.not_orientable_iff_forced_no_fixed_point`
- `PairCycleObstruction.orientable_of_local_slack`
- `PairCycleObstruction.admissible_pair_cycle_not_orientable_iff`
- `PairCycleObstruction.admissible_pair_cycle_orientable_of_local_slack`

**Evidence:** Lean verified.

**Formal-scope note:** the final global predicate is `PairRelationOrientable`, i.e. satisfiability of the exact local compatibility relations in successor order. The local equivalence with shifted basis windows is formalized. A convenience theorem packaging a satisfying assignment directly as a flattened `CyclicBasisOrder` is not yet present; do not describe that packaging theorem as Lean verified until it is added.

## Computational evidence audit

### Historical search semantics

Recovered artifact: `rank4_binary_pair_cycle_exact.py` (2026-08-06).

The script enumerates **actual binary vector-matroid pair cycles**, not abstract Boolean patterns. Vectors are nonzero elements of `GF(2)^4`; repeated vector values in nonadjacent blocks represent distinct parallel ground elements. Admissibility is exactly that adjacent pair-unions are bases, the rank-four specialization `h=2`.

The orientation relation in the script is exactly the shifted four-window relation between `P_i` and `P_{i+2}` through middle block `P_{i+1}`.

Historical repair definitions:

- **one break:** replace two adjacent pair blocks by an arbitrary ordered four-element chunk; all other pair blocks remain contiguous and freely oriented;
- **distance-two double break:** use two disjoint four-element chunks in the script's specified distance-two arrangement, with all chunk permutations and remaining pair orientations tested.

Thus the historical repair failures/successes are exhaustive only inside those stated repair classes. They do not prove or refute KUM.

### Certified strict 10-element obstruction

Verifier: `experiments/sprint2_pair_obstruction_certificate.py`.

Pair blocks over `GF(2)^4`:

`(1,2), (4,8), (1,14), (4,7), (6,9)`.

Certified facts:

- ambient labelled vector matroid has rank 4 on 10 elements;
- all five adjacent pair-unions are bases;
- local orientation relations are equality, equality, equality, inequality, equality;
- all `2^5 = 32` orientations of this fixed pair cycle fail;
- all 1022 nonempty proper subsets satisfy `2|A| < 5 r(A)`.

Therefore the witness is **strictly uniformly dense**. It is a counterexample to universal orientability of a fixed admissible pair cycle, not to KUM.

### Exhaustive re-pairing audit of the 10-element witness

Verifier/result: `experiments/sprint3_adjacent_repair_certificate.py` and `experiments/sprint3_adjacent_repair_result.json`.

For this one labelled binary matroid, the verifier exhaustively enumerates all 22,680 cyclic pair decompositions modulo rotation and internal pair order. It finds:

- 576 admissible pair cycles;
- 8 unorientable admissible pair cycles;
- every one of the 8 has an admissibility-preserving adjacent element exchange to an orientable admissible pair cycle;
- the whole 576-vertex admissible-exchange graph is connected.

An explicit repair of the original obstruction yields the cyclic element order

`2,0,3,1,5,4,6,7,9,8`,

whose ten cyclic four-windows are independently checked to be bases.

**Evidence:** exact computational certificate, executed successfully in CI. This is evidence about this labelled matroid only, not a universal repair theorem.

## Validation checkpoint

**Lean source checkpoint:** `02dfac3ffad863a6a09570b7e077a93541654f0d`

**Immutable checkpoint branch:** `checkpoint/sprint2-gcd-two-obstruction`

**CI run:** `35008387570`

Run `35008387570` passed:

- dependency lock verification;
- vendored Rank3KUM integrity;
- standalone Rank3KUM import boundary;
- Sprint 2 strict obstruction certificate;
- exact adjacent-repair certificate;
- targeted Sprint 2 Lean modules;
- final full repository `lake build`.

No custom axioms were introduced to establish the Sprint 2 results.

## Sprint closeout

**Proved / verified:** the full-support Boolean forced-transition characterization; local rank-two contraction structure of an admissible pair cycle; gcd successor-orbit characterization; one-slack-relation orientability at the relation level; strict realizable 10-element fixed-cycle obstruction.

**Refuted:** universal orientation of every admissible fixed pair cycle. The ten-element witness also demonstrates concretely that fixed-cycle failure is strictly weaker than failure of KUM, because the same matroid has repaired pair cycles and an explicit CBO.

**Still unsupported:** a universal one-step adjacent-repair theorem; a universal two-step repair theorem; connectivity of the admissible-pair-cycle graph for arbitrary matroids; a theorem that every strict gcd-two rank-four matroid admits a favorable admissible pair cycle; any claim that rank-four KUM is solved.

**Single next task:** audit one preserved 18-element historical one-break obstruction under the narrower admissibility-preserving adjacent-exchange operation. Certify the matroid and starting obstruction independently, compute only its connected admissible-exchange component, and determine its exact distance to orientability. Do not extrapolate a universal bounded-repair theorem from the outcome.
