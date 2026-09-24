# Rank-4 t=0: q=1 compressed pair-cycle route

Date: 2026-09-24.

Branch: `rank4-t0-elementary-lift-reformulation`.

Status: conceptual / computational checkpoint.  No new rank-four endpoint theorem
in this note is Lean-certified.

## 1. Scope

Fix the strict/no-dangerous rank-four t=0 branch on `4k+2` elements and an
omitted element `e`.

The minimum modular-cut rank is `q=1` exactly when `e` lies in a 2-circuit,
i.e. when it has a parallel mate.  In this case the modular cut is principal:
if `P` is the parallel class spanning `e`, every flat spanning `e`
contains `P`.

All known growing-distance witnesses (exact fixed-e distances 3,4,5,6,8) lie
in this q=1 sector.

## 2. Weighted compression gives a distinguished pair-cycle representation

Use the van den Heuvel--Thomasse weighted cyclic-order theorem with weight 4
on ordinary elements.  Compress the whole parallel class `P` to one
representative of weight `4|P|`.

Splitting its long interval back into `|P|` disjoint length-four intervals
produces an admissible rank-four pair cycle in which the P-elements occupy
one contiguous segment in the repeated +2 block orbit.

Thus q=1 comes with a much more structured representation than an arbitrary
deletion CBO or arbitrary admissible pair cycle.

This representation should be chosen before attempting local repair.

## 3. Interior segment relations

Write consecutive P-blocks in the +2 orbit locally as

`{p_j,a_j}, C_j, {p_{j+1},a_{j+1}}`

where `C_j` is the intervening two-element block.

If the pair cycle is not relation-orientable, every local Boolean relation is
a bijection.  Since `p_j` and `p_{j+1}` are parallel, the P/P cell is
forbidden.  Hence the companion/companion cell is also forbidden:

`C_j union {a_j,a_{j+1}}` is dependent,

while the two cross cells are bases.

Equivalently, in the rank-two contraction by `C_j`, the P-class and the
companion class are two distinct parallel classes.

A third parallel class is exactly local slack and therefore immediately makes
the whole pair relation system orientable.

## 4. Representation-free slack seed

Let `P` be the e-parallel class.

First, `E-P` has rank four.  Otherwise it lies in a rank-three flat of size
at least

`(4k+2)-|P| >= 3k+2`

because strict density gives `|P|<=k`, contradicting the no-dangerous
rank-three cap.

Choose a basis

`B={a,b,c,d} subset E-P`.

For `p in P`, the fundamental circuit `C_B(p)` contains at least two
elements of B; otherwise p would be parallel to an element outside P.
Choose distinct `a,b in C_B(p)-{p}` and put

`C=B-{a,b}`.

Then all three four-sets are bases:

`C union {a,b}`,
`C union {p,a}`,
`C union {p,b}`.

For two distinct parallel elements `p_1,p_2 in P`, the three pair blocks

`{p_1,a}, C, {p_2,b}`

are an admissible local pair-cycle segment.  In `M/C`, p,a,b lie in three
different parallel classes.  Therefore its local Boolean relation has three
allowed cells and is not a bijection.

Any global admissible pair cycle extending this three-block seed is
automatically relation-orientable.

This reduces the q=1 branch to the following existential extension problem.

### Prescribed slack-seed extension conjecture

Every strict/no-dangerous q=1 instance admits an admissible pair cycle
containing a three-block slack seed of the form above.

If true, q=1 is solved without any long fixed-deletion repair analysis.

## 5. Computational evidence for seed extension

The prescribed slack seed extends to a full admissible pair cycle in every
explicit growing-distance witness:

- k=3, exact deletion repair distance 3;
- k=4, distance 4;
- k=5, distance 5;
- k=6, distance 6;
- k=7, distance 8.

Backtracking search sizes for one chosen successful seed were tiny for k=3--5
and about 3.3k / 6.7k states for k=6 / k=7.

Random existential-seed stress:

- binary k=3: 25/25 instances;
- binary k=4: 15/15;
- binary k=5: 8/8;
- GF(3) k=3: 15/15;
- GF(3) k=4: 8/8.

A *particular* first slack seed need not extend.  The conjecture is explicitly
existential over the outside basis and the two chosen fundamental-circuit
elements.

## 6. Stronger repair alternative: compressed cycle endpoint theorem

There is a second route closer to existing formal repair infrastructure.

Start with any admissible pair cycle having the P-elements as one contiguous
+2-orbit segment.

Empirically:

- almost all tested compressed cycles are relation-orientable immediately;
- the old exact N=7 unorientable binary certificate has the required
  length-two P-segment and is one adjacent 2+2 repartition from orientability;
- among 10,000 random binary k=3 compressed cycles, four unorientable examples
  were found and all four repaired in one adjacent repartition;
- an additional ~24,000 endpoint-focused stress found two more unorientable
  compressed cycles, both repaired at a segment endpoint.

Candidate theorem:

> A compressed-segment admissible pair cycle is either relation-orientable or
> admits an orienting adjacent repartition in one of the two segment-endpoint
> neighborhoods.

This is stronger than needed but is especially well matched to the existing
rank-two repair lemmas.

## 7. Exact endpoint obstruction = two-class certificate

At the first P-block write

`P0={p,a},  C={c,d},  P1={p',b}`

with `p parallel p'`, and let `Y` be the block immediately before P0.

In an unorientable compressed cycle, the interior relation through C is forced.
Hence

`K={a,b,c,d}`

has rank three, while `C union {p,a}` and `C union {p,b}` are bases.

Any legal repartition of `P0 union C` must leave p in the left block:
otherwise the complementary right block contains p beside `p'` and cannot
form a basis with P1.

Thus the only nontrivial candidates are

`{p,c} | {a,d}`

and

`{p,d} | {a,c}`.

At least one is automatically valid on the right boundary because at least
one of the triples `abd`, `abc` is independent inside the rank-three set K.

Now contract the preceding block Y.  The old blocks X and P0 give bases of
the rank-two contraction `M/Y`.  The forced preceding local relation implies
that p occupies one parallel class and a the other.

For a candidate companion `x in {c,d}`:

- if x is parallel to p in `M/Y`, the candidate is illegal;
- if x is parallel to a, the candidate is legal but the preceding relation
  remains a forced bijection;
- if x belongs to a third parallel class, the candidate is legal and the
  preceding relation has at least three allowed cells, hence the entire
  pair-cycle is orientable.

Therefore the exact no-escape certificate at an endpoint is

> the movable companions meet only two parallel classes in `M/Y`: the
> red P-class and one neutral class.

This is the precise finite form of the earlier 'third-class bypass' picture.

## 8. Relationship with existing parity formalization

The existing theorem

`canonicalCrossRepair_preserves_pairRelationOrientable_of_forced`

says that a genuine cross repair which remains forced everywhere cannot change
global relation-level orientability.

Hence any repair escaping an unorientable forced cycle must create local
slack.  The endpoint classification above identifies exactly what that slack
means: access to a third class in a rank-two contraction.

This makes the q=1 target a rank-two bypass theorem rather than a parity
calculation.

## 9. Two-deletion structural input

A separate paper-level deduction appears available:

For k>=2, in the no-dangerous t=0 branch, deleting any two elements leaves a
rank-four uniformly dense matroid on `4k` elements at integral density k.

Sketch:

- ranks 1 and 2 satisfy the k,2k bounds directly from strict ambient density;
- a rank-three violation would require `3k+1` elements, whose closure is a
  dangerous hyperplane;
- rank four is bounded by the `4k`-element ground;
- the whole two-deletion minor cannot have rank <=3 when k>=2 by strict
  density.

Thus deleting two parallel elements gives a `4k` integral core.  Matroid
partition supplies k disjoint bases, although integral rank-four KUM itself is
still open, so this does not solve q=1 by itself.

It may nevertheless help prove slack-seed extension by providing a controlled
base partition.

## 10. Current best target

Do NOT return to bounded repair radius, state-local slack thresholds, mobility
potentials, or one-step saturation.  All have explicit counterexamples.

For q=1, the most focused mathematical question is now:

> Given the weighted-compression pair cycle with one contiguous P-segment,
> prove that an unorientable forced relation system has a third-class bypass
> accessible at one segment endpoint after at most one adjacent repartition.

Equivalently, prove that the two-class obstruction certificates cannot hold at
both segment endpoints under strict/no-dangerous density.

If that endpoint theorem fails, fall back to the weaker prescribed slack-seed
extension conjecture.


## 11. Correction: endpoint-only repair is false

An exact enumeration in the old binary N=7 unorientable witness kills the
strong endpoint theorem.

Fix the two parallel copies in compressed +2-segment block positions 0 and 2.
Among the compressed admissible pair cycles with this fixed indexing, there is
an unorientable state

`
((0,1),(2,3),(4,5),(6,7),(12,13),(10,11),(8,9))
`

(in the labelled version of the old witness) for which no orienting adjacent
repartition exists in either segment-endpoint neighborhood.

However, orienting adjacent repartitions do exist farther around the outside
arc (at physical boundaries 3,4,5).

So the exact two-class endpoint certificate remains mathematically correct,
but a third-class bypass need not be locally accessible at the segment
endpoint.  It may have to be routed through the complementary arc first.

The live repair strengthening is therefore only:

> every compressed-segment unorientable pair cycle admits *some* orienting
> adjacent repartition.

This weaker statement survives the exact N=7 compressed enumeration performed
here, but is not proved and should be stress-tested further.

The prescribed slack-seed extension conjecture is unaffected by this
counterexample and remains the cleaner existential target.
