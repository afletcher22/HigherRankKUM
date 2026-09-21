# Sprint 5 — six-block repair locality and exhaustive binary N=7 audit

Date: 2026-09-16.

Continuation branch: `rank4-sprint5-six-block-audit`.

Parent: `23e572d9fa4df1ce1dbc0e2f114bab1819ba5ad3`, the actual current
`rank4-research-sprint4` head inspected at continuation time.

Parent validation: GitHub Actions run `35151048294`, build job
`104979271938`, **success**. Its targeted Lean stack, every listed certificate,
dependency-lock and vendor checks, and full `lake build` all passed.
The older run `35143111762` mentioned in the Sprint 4 ledger was cancelled;
it is not the validation evidence for this parent.

No existing Lean source, project imports, dependency pins, vendor files,
or workflow definitions are changed in this continuation. The new evidence is
exact Python computation plus the checked informal locality argument below,
not new Lean formalization. The relation-to-flattened-CBO formal bridge remains
separate and unfinished. No new Actions run is needed for unchanged Lean.

## 1. Exact finite result

Every unorientable admissible binary rank-four pair cycle with seven pairs
admits a one-step legal **cross** repartition to an orientable pair cycle.
This is a computationally established finite statement, not a Lean theorem.
The five-pair case is rerun as a regression.

| Quantity | N=5 | N=7 |
| --- | ---: | ---: |
| Normalized unorientable pair cycles | 80 | 25,152 |
| Strictly uniformly dense among these | 80 | 25,152 |
| With direct orientable cross repair | 80 | 25,152 |
| With both some direct escape and some strict ascent | 80 | 24,424 |
| With escape but no strict ascent | 0 | 728 |
| With ascent but no escape | 0 | 0 |
| Failing escape-or-ascent | 0 | 0 |
| Nonidentity legal repair occurrences audited | 520 | 209,216 |

“Both” is existential separately: the escape and ascent can be different
moves. The first explicit escape printed in the output need not increase Phi.
All 728 N=7 plateaus still have a direct orientable cross repair.

These are counts of normalized represented **pair cycles**, not pairwise
nonisomorphic matroids. This result does not establish one-step repair for
arbitrary N; the existing 18-element certificate already refutes that.

### Exhaustiveness and normalization

Each binary rank-four matroid can be represented by nonzero columns of
GF(2)^4 when there are no loops. Admissibility implies that each pair is
independent and the union of the first two pairs is a basis. Choose the
ordering of those four columns and apply an invertible linear transformation
so that the first two unordered pairs are `(1,2),(4,8)`.

Every remaining unordered pair is one of the 105 two-element subsets of
`{1,...,15}`. Equal vector values in different blocks are distinct labelled
parallel elements; they are not identified as one ground element.

The DFS enumerates every continuation whose local triple relations are forced
bijections. It explicitly checks the closing adjacent basis and the final
two cyclic relations. It retains exactly odd total parity. By the established
full-support obstruction characterization, **every unorientable cycle** is
in this enumeration; pruning nonforced triples cannot omit an obstruction.
No rotation, reflection, or matroid-isomorphism count is asserted.

Each local repartition is one of the six choices of two of the four distinct
moved elements. The identity is excluded; the wholesale swap and all four
cross choices are tested. Both boundary bases are checked. A second check
scans every adjacent window of every accepted repaired cycle.

### Density and independent positive validation

Strict density is checked by occupancy in all 15 rank-one, 35 rank-two, and
15 rank-three nonzero proper ambient subspaces. These tests imply
`2|X| < N r(X)` for every nonempty proper subset: put a subset in its span;
proper rank-four subsets satisfy the inequality automatically.

The basis lookup table is independently checked by explicit span enumeration
on all 3,060 four-column multisets, including repeated values. All 241,920
admissible triples are checked for full support and correct forced pruning.

For every one of the 25,232 N=5/N=7 obstructed configurations, the verifier
constructs an actual repaired **labelled** ordering, checks it is a permutation
of all `2N` labels, and uses the independent span-rank implementation to check
every cyclic four-window. It does not merely trust the parity test for a
positive CBO. Parallel elements retain separate labels throughout.

## 2. Representation-free six-block locality argument

Assume a rank-four admissible pair cycle, odd N >= 5, and an initially
unorientable fixed cycle. Replace adjacent blocks C,D in the consecutive
neighborhood

`A, B, C, D, E, F`

by disjoint pairs Q,R with `Q union R = C union D`. Keep all other blocks
and their Boolean labels unchanged. At N=5 the first and last displayed
blocks are the same cyclic block; this causes no extra changed position.

### Admissibility

The repaired cycle is admissible iff `B union Q` and `R union E` are bases.
The middle basis `Q union R` is unchanged; every other aligned basis window
is unchanged. This is the existing two-boundary theorem specialized to rank 4.

### Orientation

Let T(X,Y,Z) be the endpoint orientation relation with full middle pair Y.
Exactly four local relations may change:

| Before | After |
| --- | --- |
| T(A,B,C) | T(A,B,Q) |
| T(B,C,D) | T(B,Q,R) |
| T(C,D,E) | T(Q,R,E) |
| T(D,E,F) | T(R,E,F) |

If any new relation has slack, the repaired cycle is orientable. Otherwise,
write epsilon(T)=0 for equality and 1 for inequality. The repaired cycle is
orientable iff the XOR of the four old epsilon values differs from that of
the four new values: all unchanged contributions cancel and the old global
parity was odd. This is valid without representability or simplicity.

### Potential change

Define `e(X,Y) = |X intersect cl(Y)| + |Y intersect cl(X)|`.
The existing Phi is `sum_j e(P_j,P_(j+2))`, by cyclic reindexing.
Only four terms change, so

```
Delta Phi = e(A,Q) + e(B,R) + e(Q,E) + e(R,F)
          - e(A,C) - e(B,D) - e(C,E) - e(D,F).
```

Consequently, from an initially obstructed odd cycle, whether a repair is
an escape or strict ascent can be decided entirely from these six blocks.
This is a **local decision criterion**, not existence of a productive repair.
It is checked against full-cycle recomputation for all 209,736 audited moves.

## 3. Binary rigidity-preserving parity conservation

The separate local audit fixes `C=(1,2), D=(4,8)` and exhausts every six-block
binary context satisfying the five adjacent basis conditions and the four
old forced-relation conditions. No closing cycle or density is assumed.

There are 256 possible left contexts `(A,B)` and 256 right contexts `(E,F)`:

- 65,536 normalized local contexts;
- 74,752 legal nonidentity repartition occurrences;
- 69,632 produce slack;
- 5,120 keep all four new relations forced;
- **zero forced-preserving parity flips**.

Thus the exhaustive binary local classification proves computationally:

> In a binary rank-four admissible odd pair cycle with N >= 5, a legal
> adjacent repartition preserving forcedness at every affected relation
> preserves the global forced parity. An escape from an obstructed cycle
> must create local slack.

The six-block normalization covers arbitrary cycle lengths in this local
statement, not merely N=7. The argument is finite and auditable but is not a
Lean proof, a representation-free theorem, or a novelty claim.

All forced-preserving local potential changes in the audit are even. Their
histogram is `-8:4, -6:32, -4:368, -2:1248, 0:1816, 2:1248, 4:368, 6:32, 8:4`.
In particular, remaining forced does **not** imply that an arbitrary chosen
repair increases Phi. Existence of a suitably chosen repair is essential.
The inverse of a legal repartition is legal, so arbitrary strict monotonicity
would also contradict reversibility whenever two obstructed states are joined.

## 4. Reproduction

Run with ordinary Python 3, no extra packages:

```bash
python3 experiments/sprint5_verify.py
```

The runner imposes a 120-second timeout per certificate and compares its JSON
output with the committed expected result. It does not write result files.
Both certificates ran successfully in the continuation environment.

## 5. Next mathematical decision

The most specific next target is a proof of binary local parity conservation
from rank-two projection geometry, followed by testing whether it extends to
nonbinary matroids. Do not silently discard parity-changing escapes in the
representation-free proof: their impossibility is only certified here for
binary representations.

For the global binary dynamics target, the finite local result reduces the
productive condition to “some legal repair creates slack OR increases Phi.”
It does not establish that some boundary always permits one. Proving that
existence statement remains the research bottleneck, especially when no
one-step escape exists as in the 18-element example.

The six-block criterion makes a finite transition/forbidden-neighborhood
approach conceivable for the binary case. Such a model must still enforce
global odd parity, cyclic wraparound, and strict density. Do not infer a
global repair theorem solely from individually permissible local contexts.

No unrestricted N=9 enumeration, generalized matroid search, universal repair
claim, or KUM resolution is included in this continuation.
