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

### t=1 — direct construction (new closure)

Here G is the unique dangerous hyperplane, so

    |G| = 3k+1,      r(G)=3,

and its complement C has |C|=k+1.

The restriction M|G is uniformly dense of rank 3.  For rank-1 and rank-2
subsets this follows from the integer consequences of strict rank-4 density,
and the whole set has size 3k+1.  Hence the rank-3 theorem supplies a cyclic
basis order

    g_0,...,g_{3k}.

Call the cyclic edge

    P_i={g_i,g_{i+1}}

C-good when

    r(P_i ∪ C)=4.

Equivalently, C has rank 2 in M/P_i.  Since P_i lies in the flat G while
every c∈C lies outside G, every element of C is a nonloop in M/P_i.

The t=1 construction splits according to the cyclic pattern of good edges.

#### Two elementary rank-2 selection lemmas

1. **Common pair.**  Two loopless rank-2 matroids on the same ground set have
   a common two-element basis.

   Proof: take a basis {a,b} of the first matroid.  If there is no common
   basis, a and b are parallel in the second.  For arbitrary x, either
   {a,x} is a basis of the first, forcing x parallel to a in the second, or
   x is parallel to a in the first, in which case {b,x} is a basis of the
   first and again x is parallel to a in the second.  Thus the second matroid
   would have rank at most 1, contradiction.

2. **Two-matroid path.**  If the common ground set has at least three
   elements, then for two loopless rank-2 matroids N_1,N_2 there are distinct

       c_0,c_1,c_2

   such that {c_0,c_1} is a basis of N_1 and {c_1,c_2} is a basis of N_2.

   In a loopless rank-2 matroid on at least three elements, some element has
   at least two possible basis partners: if there are two parallel classes,
   choose an element in a smallest class; with at least three classes this is
   immediate.  Choose c_1 with two N_1-partners, choose any N_2-partner c_2,
   and then choose an N_1-partner c_0 distinct from c_2.

#### How many C-good core edges are forced?

The only delicate case is r(C)=2.

- r(C)=0 or 1 is impossible by strict density because |C|=k+1.
- If r(C)=4, every edge is C-good.
- If r(C)=3, a bad edge has both endpoints in

      G ∩ cl(C).

  This intersection has rank at most 2 because G and cl(C) are distinct
  rank-3 flats.  Hence three consecutive elements of the core CBO cannot all
  lie in it.  In particular two bad edges cannot be consecutive.

Now suppose r(C)=2 and put

    K=(M/C)|G.

Then K has rank 2.  Every three consecutive g_i have rank 2 in K.  Indeed if
such a triple had K-rank at most 1, then C together with that triple would
have rank at most 3.  But the triple is a rank-3 basis of the flat G, so its
ambient closure is G; adding C outside G must raise rank to 4.

Thus an edge P_i is bad exactly when its two endpoints have K-rank at most 1.
Moreover two consecutive bad edges

    P_{i-1}, P_i

occur exactly when their shared vertex g_i is a loop of K.  If g_i were a
nonloop, both neighboring elements would lie in the same rank-1 flat as g_i,
contradicting rank 2 of the consecutive triple.

Let l be the number of loops of K.  These loops are exactly

    G ∩ cl_M(C).

Since cl_M(C) is a rank-2 flat containing the k+1 elements of C, strict
density gives

    |cl_M(C)| ≤ 2k,

hence

    l ≤ k-1.

Assume now that no two C-good edges are consecutive.  Write a cyclic binary
word on the 3k+1 core edges, with 1=good and 0=bad.  There are no adjacent
1s.  In the r(C)=2 case, the number of adjacent 00 pairs is exactly l, by the
loop characterization above.

If g and b are the numbers of good and bad edges, cyclic transition counting
gives

    b = g + l,

hence

    3k+1 = 2g+l

and therefore

    g = (3k+1-l)/2 ≥ k+1.

For r(C)=3, bad edges are themselves nonadjacent; combined with the assumption
that good edges are nonadjacent this gives at least k+1 good edges as well.
The r(C)=4 case cannot occur under the no-adjacent-good assumption.

So in every no-adjacent-good case there are at least k+1 good edge starts on
a cycle of length 3k+1.  Their cyclic gaps sum to 3k+1.  Since no gap is 1
and

    (3k+1)/(k+1) < 3,

some gap is exactly 2.  Therefore there are C-good edges

    P_i={g_i,g_{i+1}},
    P_{i+2}={g_{i+2},g_{i+3}}.

#### Case A: adjacent C-good edges

Suppose P_{3k-1} and P_{3k} are C-good after rotating the core order.  The
two restrictions

    (M/P_{3k-1})|C,
    (M/P_{3k})|C

are loopless rank-2 matroids.  By the common-pair lemma choose
c_*,c_0∈C forming a basis in both.

Use the type pattern

    (C G G G)^k C G.

Place c_*,c_0 in the two C positions that occur in the two exceptional
windows; fill the remaining C positions arbitrarily.

Every ordinary four-window is one C element plus three consecutive G elements,
hence a basis.  The only exceptional windows are

    G C G C,
    C G C G,

and both are bases because the same C-pair is a basis in the two contractions.

#### Case B: no adjacent C-good edges

By the counting argument choose good edges P_0 and P_2 after rotation.  The
matroids

    (M/P_0)|C,
    (M/P_2)|C

are loopless rank 2.  Since k≥2, |C|=k+1≥3, so the two-matroid path lemma gives
distinct c_0,c_1,c_2∈C such that

    {c_0,c_1} is a basis in (M/P_0)|C,
    {c_1,c_2} is a basis in (M/P_2)|C.

Use the type pattern

    C G G C G G (C G G G)^(k-1).

Put c_0,c_1,c_2 in the first three C positions and fill the remaining C
positions arbitrarily.

There are exactly two windows containing two C elements:

    c_0 g_0 g_1 c_1,
    c_1 g_2 g_3 c_2.

They are bases by the two chosen contraction bases.  Every other four-window
contains exactly one C element and three consecutive elements of the core CBO,
so it is automatically a basis.

Hence every strict rank-4 instance with exactly one dangerous hyperplane also
has an explicit cyclic basis ordering.  No deletion/lifting theorem is needed.

This closes the t=1 case informally, subject only to routine formalization of
the two elementary rank-2 selection lemmas and the cyclic edge-counting
argument.

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
3. Formalize the direct t=2 construction and its bad-core-edge counting lemma.
4. Formalize the now-complete t=1 good-edge counting argument and the two
   elementary rank-2 selection lemmas.
5. Return to deletion-CBO lifting only for t=0.

This route is attractive because t=3 is exactly the case where direct
insertion fails most systematically, yet it becomes the easiest case after
using dangerous-hyperplane geometry.
