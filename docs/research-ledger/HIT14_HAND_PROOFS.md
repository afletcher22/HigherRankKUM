# The hitting lemma at k = 3 with a heavy flat: human proofs

**Status.** These are complete human proofs of the two n = 14 hitting cases that were SAT
certificates: `hit14g` (a 9-plane, 55,754 hints) and `hit14line` (a 6-line and no 9-plane,
842,574 hints). They are formalized in `probes/Probe/Rank4/HitThree.lean` on branch
`probe/hit14-human` (`Hitting.HitThree.hitG`, `Hitting.HitThree.hitLine`). With them and Lemma H,
the hitting lemma at k = 3 needs no SAT.

---

## 0. Setting

M is a rank-4 matroid on 14 elements, strict with t = 0 (`StrictT0 M 3`). Equivalently: M has no
loops, every point (rank-1 flat) has at most 3 elements, every line at most 6, every plane at
most 9. We write cl for closure, X + e for X ∪ {e}, and "k-point", "k-line", "k-plane" for a
flat of rank 1, 2, 3 with k elements.

A basis S is *deletable* if M ∖ S is uniformly dense at ratio 10/4, that is, every point, line
and plane F of M has |F − S| at most 2, 5 and 7. Under the profile this says that S meets every
3-point, every 6-line and every 8-plane, and meets every 9-plane at least twice
(`deletable_of_meetsDemands`).

Lemma H covers the case with no 9-plane and no 6-line. Two standard facts are used throughout.

* **(P)** A set of rank at most 1 that meets a flat lies in it. So two points either coincide or
  are disjoint.
* **(D)** If X ⊄ F for a flat F, then r(X ∩ F) < r(X). In particular two distinct flats of rank r
  meet in a set of rank less than r.

---

## 1. A 9-plane K (`hitG`; the choice lemma of Theorem G at k = 3)

This is the k = 3 case of the choice lemma in `RANK4_HEAVY_FLAT_SPLICE.md` §7. The proof below
replaces its three-way split on r(C) with one argument.

Let C = E − K, so |C| = 5. M|K has rank 3 and at most 3 r(X) elements in every X ⊆ K, so by
Edmonds K splits into three bases D₀, D₁, D₂ of M|K, each an independent triple.

**Lemma G1 (choice of c).** Some c ∈ C has the following properties, where C₀ = C − c:
(a) every subset of C₀ of rank at most 1 has at most 2 elements;
(b) C ⊆ cl(C₀).

*Proof.* If C contains a set Q of rank at most 1 with 3 elements, take c ∈ Q. For (a), let
Y ⊆ C₀ have rank at most 1 and 3 elements. If Y meets Q, then Y + c lies in one point by (P),
which then has 4 elements. Otherwise |Y ∪ Q| = 6 > |C|. For (b), c is parallel to the other
elements of Q, which lie in C₀. If C has no such set, (a) holds for every c. Take c outside a
basis I of M|C; such a c exists because |I| ≤ 4 < 5. Then C ⊆ cl(I) ⊆ cl(C₀). ∎

Call two of the triples, Da and Db, *light* if every plane F ≠ K with C ⊆ F has
|F ∩ Da| + |F ∩ Db| ≤ 3.

**Lemma G2 (a light pair exists).** Some two of D₀, D₁, D₂ are light.

*Proof.* Let F ≠ K be a plane through C. Then |F ∩ K| ≤ 9 − 5 = 4. By (D), F ∩ K has rank at
most 2, so F meets each triple in at most 2 elements. Call F *heavy* for a triple it meets twice.
A pair that is not light has a common heavy plane, and no plane is heavy for all three triples
(that would need 6 elements of F ∩ K).

Suppose no pair is light, with common heavy planes F₀₁, F₀₂ and F₁₂. Then F₀₁ ≠ F₀₂ and
F₀₁ ≠ F₁₂. D₀ meets F₀₁ and F₀₂ twice each, so it meets F₀₁ ∩ F₀₂, say in p. Likewise D₁ meets
F₀₁ ∩ F₁₂, say in q.

Now F₀₁ ∩ F₀₂ is a set of rank at most 2 by (D), and it contains C, which has rank at least 2
because |C| = 5. So F₀₁ ∩ F₀₂ ⊆ cl(C), and likewise F₀₁ ∩ F₁₂ ⊆ cl(C). Also r(cl(C)) ≤ 2, so
|cl(C)| ≤ 6, and cl(C) contains the 5 elements of C. Hence |cl(C) ∩ K| ≤ 1, so p = q. But
D₀ and D₁ are disjoint. ∎

**Lemma G3 (the deletable basis).** Let Da, Db be light, De the third triple, and c as in G1.
Then S = De + c is a deletable basis.

*Proof.* S is a basis because c ∉ K = cl(De). Let X ⊆ E − S have rank j. We show 4|X| ≤ 10j.
X ∩ K lies in Da ∪ Db and X − K lies in C₀, so

  |X| ≤ |Da ∩ X ∩ K| + |Db ∩ X ∩ K| + |X − K|, with |X − K| ≤ 4.

Each of the first two terms is at most r(X ∩ K), since Da and Db are independent.

* If X ⊆ K, then |X| ≤ 2j.
* Otherwise r(X ∩ K) ≤ j − 1 by (D), so |X| ≤ 2(j − 1) + |X − K|.
  * j = 1: X ∩ K is empty, and |X − K| ≤ 2 by G1(a).
  * j = 4: |X| ≤ 6 + 4 = 10.
  * j = 2 or 3 with |X − K| ≤ 3: |X| ≤ 5 or 7.
  * |X − K| = 4: then X − K = C₀, so cl(X) ⊇ cl(C₀) ⊇ C by G1(b).
    * At j = 2, cl(X) has at most 6 elements, 5 of them in C, so |X ∩ K| ≤ 1 and |X| ≤ 5.
    * At j = 3, cl(X) is a plane through C, and cl(X) ≠ K because c ∈ cl(X). Lightness gives
      |X ∩ K| ≤ 3, so |X| ≤ 7.

In every case 4|X| ≤ 10j. ∎

G2 and G3 prove the case.

---

## 2. A 6-line L and no 9-plane (`hitLine`)

Every plane now has at most 8 elements. In particular a set of rank at most 3 has at most 8
elements. Let X = E − L, so |X| = 8.

**Lemma L1.**
(a) Every 3-point lies in L.
(b) Two distinct 6-lines are disjoint.
(c) There is at most one 6-line other than L.

*Proof.* (a) A 3-point Q that does not meet L is disjoint from it by (P). Then Q ∪ L has rank at
most 3 and 9 elements. (b) If two 6-lines meet, their intersection has rank 1 by (D), so it has at
most 3 elements. Submodularity gives r(L ∪ L′) ≤ 3, and |L ∪ L′| ≥ 9. (c) Two more 6-lines would
be disjoint from L and from each other, and three disjoint 6-lines do not fit in 14 elements. ∎

**Construction.** Take x ∈ X on the other 6-line, if there is one (otherwise any x ∈ X). Take
y ∉ cl(L + x); such a y exists because |cl(L + x)| ≤ 8. Take a, b ∈ L non-parallel, chosen as in
L3 below. Then S = {a, b, x, y} is a basis: cl({a, b}) = L, x ∉ L and y ∉ cl(L + x).

S meets every 3-point if {a, b} does (L1(a)), and it meets every 6-line (L1(b, c) and the choice
of x). There are no 9-planes. It remains to handle 8-planes F. If F contains x, y or L, it meets
S. Otherwise:

**Lemma L2.** Let F be an 8-plane with x, y ∉ F and L ⊄ F. Then L ∩ F is a point with 2 or 3
elements. If it has 2, then F = F₀ := cl(X − {x, y}).

*Proof.* L ∩ F is a flat of rank at most 1 by (D), so it has at most 3 elements. F − L avoids
L, x and y, so |F − L| ≤ 14 − 6 − 2 = 6, and |L ∩ F| ≥ 2. If |L ∩ F| = 2, then |F − L| = 6, so
F − L = X − {x, y} =: W. If r(W) ≤ 2, then cl(W) is a 6-line other than L, with cl(W) = W. By the
choice of x, it contains x. But x ∉ W. So r(W) = 3 = r(F), and F = cl(W). ∎

**Lemma L3.** There are non-parallel a, b ∈ L such that {a, b} meets every 3-point in L and
also L ∩ F₀ if that set is a point.

*Proof.* The points to meet are pairwise disjoint subsets of L by (P). All but possibly one of
them, L ∩ F₀, have 3 elements. Three of them would need 3 + 3 + 1 > 6 elements, so there are at
most two. Take a and b in two of them, or a in one and b ∈ L − cl(a), or any non-parallel pair if
there are none. ∎

By L2 and L3, S meets every 8-plane, so S meets the demands. ∎

---

## 3. Checks

`experiments/rank4_heavy_flat_splice/check_hit14.py` generated 390 random representable instances
over GF(3), GF(5) and GF(7), biased toward heavy configurations: several 9-planes, C of rank 2 or
3, a 3-point in C, two 6-lines, and heavy planes through points of L. For every instance it
enumerated every choice the proofs allow: all Edmonds partitions, all admissible c and light pairs
for G, and all x, y, a, b for L. In total 367,802 choices were tried (325 instances with a 9-plane,
65 with a 6-line and no 9-plane), and every one gave a deletable basis. The proofs do not depend
on this check.
