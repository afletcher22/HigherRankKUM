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

## Reading

* Keeping an existing ordering fixed fails; re-ordering inside blocks is what matters.
* Splitting every basis into two blocks is always possible (Greene–Magnanti), and refining such a
  split decouples into independent cycles in contractions of smaller rank. A blocked case is one
  specific split of one basis.
* In the rank induction the inserted elements never share a window, so reinsertion is a bipartite
  matching. The success rate falls by a roughly constant factor per added basis, which looks like
  independent local events.
