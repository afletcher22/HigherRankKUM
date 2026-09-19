# Rank-4 dangerous-core route

Status: research checkpoint after the density-slack deletion theorem and the
n=6 boundary closure.  This note records a new structural route for the strict
rank-4 case |E| = 4k+2.

## 1. Why this route

The deletion-CBO lifting program remains viable, but direct insertion is known
to fail in the sharp k=2 family, and the attempted formal
deletion-CBO-to-pair-cycle plumbing was disproportionately expensive in
dependent Fin arithmetic.  That experimental module was parked after the
generic full-order-to-pair-cycle and relation-orientability-to-CBO bridges had
already gone green.

The dangerous-hyperplane theorem gives a different case split that appears to
capture exactly where direct insertion becomes difficult.

Let

- M have rank 4 and |E| = 4k+2;
- M be strictly uniformly dense;
- a dangerous hyperplane mean a rank-3 flat of size 3k+1;
- t be the number of dangerous hyperplanes.

The existing theorem gives t <= 3, pairwise disjoint dangerous-hyperplane
complements, each of size k+1, and exact good-deletion count

    |Good| = 4k+2 - t(k+1).

## 2. The dangerous core

For distinct dangerous hyperplanes H_1,...,H_t, put

    C_i = E \ H_i,
    G   = H_1 ∩ ... ∩ H_t
        = E \ (C_1 ∪ ... ∪ C_t).

The complements C_i are pairwise disjoint and each has size k+1.  Consequently

    |G| = 4k+2 - t(k+1).

The expected exact ranks are

| t | |G|   | r(G) |
|---|-------|------|
| 0 | 4k+2  | 4 |
| 1 | 3k+1  | 3 |
| 2 | 2k    | 2 |
| 3 | k-1   | 1 |

For t=1 this is immediate.  For t=2, H_1∩H_2 has rank at most 2 by the
existing dangerous-intersection theorem and cardinality 2k; strict density
rules out rank <=1.  For t=3, H_1∩H_2 is a rank-2 flat of size 2k and the
triple intersection is a proper flat inside it.  Equal rank would force the
two flats to agree, while strict density/looplessness rules out rank 0.
Hence the triple core has rank 1.

More generally, for

    F_i = G ∪ C_i = ∩_{j != i} H_j,

one gets rank r(G)+1.  Thus, after contracting G, each C_i is a rank-1
parallel class and the t classes form the rank-t quotient directions.

This recovers the exact geometry observed in the sharp binary examples rather
than merely an isomorphic special case.

## 3. The t=3 case is explicitly constructible

Assume t=3 and write the three complement classes as A,B,C.

Then

    |G| = k-1,       r(G)=1,
    |A|=|B|=|C|=k+1.

Moreover

    G∪A, G∪B, G∪C

are rank-2 flats (the pairwise intersections of the three dangerous
hyperplanes).

Each of A,B,C has rank 2.  Indeed each lies in a rank-2 flat, while rank <=1
would contradict strict density because its size is k+1.

### Three-element selection inside each side class

In any loopless rank-2 matroid on at least three elements, there exist
distinct q,p,d such that

    {d,q} and {d,p}

are independent.

Proof sketch: take a basis {u,v} and a third element w.  If w is nonparallel
to both, use d=w.  If w is parallel to u, use d=v and partners u,w; the other
case is symmetric.

Choose such triples

    q_A,p_A,d_A,
    q_B,p_B,d_B,
    q_C,p_C,d_C.

Enumerate the remaining k-2 elements of each side class arbitrarily, and
enumerate G as g_1,...,g_{k-1}.

### Candidate full cyclic order

Use the type pattern

    (A B C G)^(k-1) A B C A B C.

Concretely, put q_A,q_B,q_C in the first ABC block; use the remaining
non-special side elements in the other prefix blocks; then use

    p_A,p_B,p_C,d_A,d_B,d_C

for the final ABCABC tail.

### Why every 4-window is a basis

Any window containing G has exactly one element from each of G,A,B,C.

For example, with g∈G, a∈A, b∈B, c∈C:

1. g and a span the rank-2 flat G∪A;
2. b lies outside that flat but inside the appropriate dangerous hyperplane,
   so rank rises to 3;
3. c lies outside that rank-3 dangerous hyperplane, so rank rises to 4.

Hence {g,a,b,c} is a basis.

The only windows not containing G occur in the six-window tail/wrap region.
Each consists of one element from two side classes and two elements from the
third.  The duplicated pair is one of

    {p_A,d_A}, {d_A,q_A},
    {p_B,d_B}, {d_B,q_B},
    {p_C,d_C}, {d_C,q_C}.

Every such pair is independent by construction.  An independent pair in A
spans the rank-2 flat G∪A; adding an element of B raises rank to 3 inside the
corresponding dangerous hyperplane, and adding C raises rank to 4.  The same
argument applies cyclically.

Therefore the displayed order is a CBO.

This would settle the entire t=3 case directly, with no deletion CBO, no
insertion theorem, and no repair graph.

## 4. Constant-defect patterns for t=2 and t=1

The same quotient/core viewpoint gives promising direct patterns.

### t=2

Here G is a uniformly dense rank-2 flat of size 2k, and A,B are the two
(k+1)-element complement classes.  Let a cyclic rank-2 basis ordering of G
supply the G positions.

The type pattern

    (A B G G)^(k-1) A B G B A G

has only four nonstandard windows, all with composition 2+1+1:

    ABGB, BGBA, BAGA, AGAB.

These split into two local conditions:

- one independent B-pair together with one chosen G element must span the
  rank-3 flat G∪B;
- one independent A-pair together with another chosen G element must span
  G∪A.

Every other 4-window is automatically one A, one B, and a consecutive basis
pair of G.

A second pattern

    (A B G G)^(k-1) A B A B G G

has only three exceptional windows but introduces a coupled ABAB basis test;
the ABGBAG tail is currently preferable because it decouples the A and B
defects.

The remaining issue is choosing the two distinguished G elements to be
consecutive/nonparallel while avoiding the rank-1 intersections determined by
the chosen A and B pairs.

### t=1

Here G is a uniformly dense rank-3 flat of size 3k+1 and C is the
(k+1)-element complement.

Using a rank-3 CBO of G, the type pattern

    (C G G G)^k C G

has only two exceptional windows:

    G C G C,
    C G C G.

Thus the problem reduces to finding a two-element set Q⊂C that is a base in
two rank-2 contractions determined by two adjacent G-pairs.  This is a
constant-size/common-base defect rather than a global lifting problem.

## 5. Empirical checks

Fresh seeded binary rank-4 n=10 tests agree strongly with the dangerous-count
split.

In an initial sample of 40 strict matroids:

- t=0: all 9 examples had a direct lift for all 10 deletions;
- t=1: all 23 examples had a direct lift for all 7 good deletions;
- t=2: five of six examples had direct lifts for all 4 good deletions; one
  example had 2 direct-liftable and 2 nonliftable good deletions;
- t=3: both examples had the unique good deletion and neither deletion CBO was
  directly insertable.

In a second seeded sample:

- 20 tested t=0 examples again had direct lifts for every deletion;
- 30 t=1 examples had no nonliftable good deletion;
- among 30 t=2 examples, six had some nonliftable good deletions but every
  matroid still had at least one directly liftable good deletion;
- all 20 t=3 examples had no directly insertable good deletion.

The fixed direct patterns were also tested:

- all 23 initial t=1 examples admitted (CGGG)^2 CG;
- all 6 initial t=2 examples admitted ABGG ABGBAG (equivalently the fixed
  t=2 constant-defect pattern);
- 20 additional t=3 examples admitted ABCG ABCABC.

These are experiments, not proofs.

## 6. Revised rank-4 research priority

1. Formalize the dangerous-core rank/cardinality structure, especially the
   t=3 rank-1 core theorem.
2. Formalize the explicit t=3 CBO construction.
3. Prove the small local selection lemma needed by the t=2 ABGBAG defect.
4. Prove the two-contraction common-pair lemma needed by the t=1 CG tail.
5. Return to deletion-CBO lifting primarily for t=0, and possibly as a backup
   for t=1/t=2.

This route is attractive because t=3 is exactly the case where direct
insertion fails most systematically, yet it becomes the easiest case after
using dangerous-hyperplane geometry.
