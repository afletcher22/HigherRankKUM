# Chains of bases: exploratory enumeration (2026-11-10)

Plain enumeration in Python (exact rank computations over GF(2) or GF(3), or a list of bases; 0/1
matrix products). No SAT solver. Nothing in the Lean development depends on these scripts. They
were written to find out which statements are false before trying to prove anything. "Exhaustive"
means every case among binary matroids of that size; it says nothing about other matroids.

Run from this directory. Needs Python 3.10+ and numpy.

## Setting

A *chain* is a cyclic sequence of disjoint bases `B_1, ..., B_k` of a rank-`r` matroid. An
*interval ordering* orders each basis so that the concatenation is a cyclic basis ordering. This
holds exactly when, for every `i`, each suffix of `B_i` together with the complementary prefix of
`B_{i+1}` is a basis (a serial exchange). So an interval ordering is a closed walk through `k`
relations between orderings, decided by boolean matrix products (`chainlib.py`).

## Results

| Statement | Script | Result |
|---|---|---|
| One-point insertion into a fixed ordering of `M \ e` | `puncture.py` | fails for R10: every element, all 768 orderings; R10 has 288 cyclic basis orderings |
| Some interval ordering exists (any `k` bases, any cyclic order) | `cyclic_chain.py`, `chain_adv.py`, `chain_vamos.py`, `fast5.py` | no failure: rank 3 over GF(2) exhaustive (`k = 3`), rank 4 over GF(2) exhaustive (`k = 3`, 26,080 cases), R10 pair with every third basis (83,328), 40,000 random triples in rank 5, Vámos |
| Some ordering of two bases extends with the third inserted contiguously | `insert5.py`, `fast5.py` | no failure in the same rank-5 runs; "every ordering extends" fails in about half the instances |
| Prefix freedom: any subset of a basis can be an initial segment | `pf_exhaust.py`, `pf_more.py`, `fast5.py` | holds for two bases (GF(2) exhaustive in ranks 3, 4, 5; Vámos exhaustive) and for three bases in ranks 3 and 4 (GF(2) exhaustive); **fails** for three bases in rank 5 (19 of 40,000 random triples) |
| Prescribed initial segments on both of two bases | `pf_exhaust.py` | fails: 3,688 of 44,630 symmetric-exchange pairs in rank 5 |
| Cyclic-window invariants span all invariants of multidegree `(r, ..., r)` | `span_test.py` | true for `r = 2` (`n = 4..7`) and `(4, 6)`; false for `(3, 6)` (35 of 40) and `(3, 7)` (205 of 225) |
| Rank induction: contract `x0`, order the rank `r - 1` remainder, match the removed elements to the slots | `schemeR.py`, `schemeR5.py` | works for R10 from all 90 choices; strict binary matroids, share of sampled orderings that extend: rank 5: 41.7% / 16.3% / 7.4% for 2 / 3 / 4 bases; rank 4: 58.6% / 24.2% / 13.0% (`schemeR5_result.txt`) |
| Pair split of the 4-blocks after a root split (rank 5, tree `1 + (2 + 2)`) | `pairsplit_chain.py`, `pairsplit_adv.py` | closes for every valid root split tested (about 189,000 in strict binary matroids and `M(K_6)`, 125,000 in sparse random chains); the 4-blocks then close completely in 99.7% / 99.93% / 99.99% of root splits for 2 / 3 / 4 bases (`pairsplit_result.txt`) |
| The same, two bases | `pairsplit_two.py` | proved over `F_2` by an identity (see the note); no failure sampled over `F_3`, `F_5`; the shapes `(1, 1, 3)` and, in rank 4, `(1, 1, 2)` do fail |
| "The pair split always closes" | `pairsplit_rigid_example.py` | **false**: a rigid chain of three bases with 3-cycle holonomy (not strict) |
| A cycle of pair-split relations with one slack relation closes | `pairsplit_local.py`, `pairsplit_union.py` | true for all relation types over `F_2` (51), `F_3` (434) and for the 1,664 types found over `F_2`, `F_3`, `F_5`, `F_7`; 36 tight types |
| The pair split closes for every root split of a strict matroid | `pairsplit_tightsearch.py` | **false**: 96 strict chains over `F_2` with two rigid relations have one failing root split each; all their other root splits close completely |
| Some admissible choice for two consecutive bases gives a slack relation | `pairsplit_pairs.py` | true for 98.0% of the 9,999,360 pairs of bases over `F_2`; the 202,320 exceptions fall into 28 classes |
| Three bases with every consecutive pair an exception | `pairsplit_triples.py` | 949,440 chains, 3,720 strict; each strict one has 13 root splits and all close completely |
| Every chain of three bases has a root split whose 4-blocks close completely | `pairsplit_structured.py` | no failure in 12,000 structured chains over `F_2` (4,436 strict), nor in any earlier run |
| Slack lemma for full orderings | `slack_orders.py` | triples: holds over `F_2`, `F_3`, `F_5`; 4-blocks over `F_2`: vacuous, no relation meets all 24 bijections |
| Slack lemma for all matroids: two matroids of rank 4 on `W + W'` with no common basis meeting `W` in two elements are both tight, and both contain a bijection | `slack_allmatroids.py`, `slack_allmatroids_check.py` | true for all 5,828,710 labelled matroids in which `W`, `W'` are bases (618,214 relations, 1,695 classes, 43 tight); the relations are closed under composition, so it holds for cycles of every length |
| The enumeration is complete | `slack_allmatroids_validate.py` | contains every relation of `GL_4(F_2)`, `GL_4(F_3)` and of samples over `F_5`, `F_7`, `F_11`; 3,200,452 sparse paving matroids, equal to an independent count |
| Rank criterion for blocked pairs; blocked pairs of total support | `slack_blocked.py` | criterion agrees on every sampled pair (`F_2`, `F_3`, `F_7`); total support: only pairs of permutation matrices over `F_2`, 8 support patterns over `F_3` |
| Blocked pairs of total support, all matroids | `slack_total_support.py` | 1,671 pairs, 8 pairs of exchange graphs up to symmetry (the same 8 as over `F_3`); one member is rigid, or both have shape `2+1+1`, or the shapes are `2+1+1` and `3+1` |

## Reading

* Keeping an existing ordering fixed fails; re-ordering inside blocks is what matters.
* Splitting every basis into two blocks is always possible (Greene–Magnanti), and refining such a
  split decouples into independent cycles in contractions of smaller rank. A blocked case is one
  specific split of one basis.
* In the rank induction the inserted elements never share a window, so reinsertion is a bipartite
  matching. The success rate falls by a roughly constant factor per added basis, which looks like
  independent local events.
* Fixing only the single elements and leaving the 4-blocks free behaves the opposite way: almost
  every root split closes, and the failure rate falls as bases are added. See Section 8 of
  `docs/research-ledger/BEYOND_RANK4_ROUTES.md`.
* The slack lemma is a property of all matroids, not of small fields: it was checked on the
  complete list of rank-4 matroids on 8 elements, and the blocked pairs reduce to eight shapes
  (Section 9 of the note).
