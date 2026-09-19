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

### t=2 — direct construction (checked informal)

Here G is a rank-2 flat of size 2k, while A and B are the two disjoint
dangerous-hyperplane complements, each of size k+1.  The two dangerous
hyperplanes are

    G∪A,   G∪B.

The restriction to G is uniformly dense of rank 2 at integral density k:
rank-1 subsets have size at most k by strict rank-4 density, and the
rank-0/rank-2 cases are automatic.  Hence the internal rank-2 theorem supplies
a cyclic basis order

    g_0,...,g_{2k-1}

of G.

#### Good core elements for a side class

For X=A or B, call g∈G X-good if there are x_1,x_2∈X such that

    {g,x_1,x_2}

is a basis of the rank-3 hyperplane G∪X.

The X-bad set has size at most k-1.

Indeed strict density rules out r(X)=1 because |X|=k+1.

- If r(X)=3, X spans G∪X.  Any nonloop g∈G extends to a basis using two
  elements of X, so every g is X-good.
- If r(X)=2, an element g is bad exactly when

      g ∈ G ∩ cl(X).

  The rank-2 flat cl(X) contains the k+1 elements of X as well as this bad
  subset of G.  Strict rank-4 density bounds every rank-2 flat by 2k
  elements, so

      |Bad_X| ≤ 2k-(k+1)=k-1.

#### An oriented adjacent core basis good for both sides

Orient the 2k adjacency edges of the cyclic rank-2 order.  We need an edge

    g_j -> g_{j+1}

whose tail is B-good and whose head is A-good.

If no such edge existed, every oriented edge would be covered either by a
B-bad tail or by an A-bad head.  The number of edges with B-bad tail is
exactly |Bad_B|, and cyclic successor is a permutation, so the number with
A-bad head is exactly |Bad_A|.  Thus all 2k edges would be covered by at most

    (k-1)+(k-1)=2k-2

edges, impossible.

Choose such an edge and rotate the core CBO so that

    g_B=g_{2k-2},   g_A=g_{2k-1}.

Choose b_1,b_2∈B with {g_B,b_1,b_2} a basis of G∪B, and choose
a_1,a_2∈A with {g_A,a_1,a_2} a basis of G∪A.

#### Full cyclic order

Use the type pattern

    (A B G G)^(k-1) A B G B A G.

Place b_1,b_2 in the two exceptional B positions.  Place a_1,a_2 in the
exceptional A position and the wraparound first A position.  Fill all remaining
A/B positions arbitrarily with the remaining elements, and place the rotated
core CBO in the G positions.

Every ordinary 4-window contains one A, one B, and two consecutive G elements.
The G pair spans the rank-2 flat G; adding A spans G∪A, and adding B raises
rank to four.  Hence every ordinary window is a basis.

The only exceptional windows are

    A B G B,
    B G B A,
    B A G A,
    A G A B.

The first two contain {g_B,b_1,b_2}, a basis of G∪B, plus an A element
outside that hyperplane.  The last two contain {g_A,a_1,a_2}, a basis of
G∪A, plus a B element outside that hyperplane.  Hence they are bases as well.

Therefore every strict rank-4 instance with exactly two dangerous hyperplanes
has an explicit cyclic basis ordering.  No deletion/lifting theorem is needed.

This proof is checked informal mathematics and is not yet Lean-certified.

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
3. Formalize the now-complete direct t=2 construction and its bad-core-edge counting lemma.
4. Prove the two-contraction common-pair lemma needed by the t=1 CG tail.
5. Return to deletion-CBO lifting primarily for t=0, and only as a backup for t=1.

This route is attractive because t=3 is exactly the case where direct
insertion fails most systematically, yet it becomes the easiest case after
using dangerous-hyperplane geometry.
