# Rank 5: first probe of the extension route

Date: 2026-09-26.

Rank 5 is prime, so full rank-5 KUM follows from the divisible case (`n = 5k`) by
`solvesKUMAtRank_of_prime`. The rank-4 proof of the divisible case (Theorem D) suggests a route:

1. an Edmonds partition into bases, from van den Heuvel–Thomassé;
2. induction, deleting one basis `S`;
3. the extension theorem X′₅(N): a cyclic basis ordering of `M \ S` on `N` elements extends to
   one of `M`;
4. a base case KUM(5,10).

This note records the first SAT experiments on step 3. They are negative.

## Encoder

`experiments/rank4_heavy_flat_splice/ext_rank_r.py r N [w] [dense]` generalizes `ext_witness.py`
(the rank-4 X′ encoder) to rank `r`:

* rank axioms on every block made of `S` and `w` cyclically consecutive elements of the ordering;
* unit clauses making `S` and every `r`-window of the ordering a basis;
* one clause per interleaving (an order of `S` and a multiset of insertion gaps) saying that some
  merged window is not a basis.

`dense` adds the density of `M` and of `M \ S` as lower bounds on ranks.

In rank 4 it reproduces the known results: X′₄(8) is UNSAT (it holds), and X′₄(6) is SAT (it
fails).

## Results in rank 5

| N | w | density | result |
|---|---|---|---|
| 10 | 7 | no | SAT (95 s) |
| 10 | 8 | no | SAT (111 s) |
| 10 | 9 | no | SAT (154 s) |
| 10 | 7 | yes | SAT (86 s) |
| 15 | 7 | no | SAT (247 s) |

A SAT answer means either that X′₅(N) fails, or that the local encoding is too weak to
refute it. At `N = 10` the answer stays SAT with blocks covering 9 of the 10 elements, and with
density added. This suggests a genuine failure at `N = 10`, as in rank 4 at `N = 6`.

## Consequences and next steps

* The rank-4 shape (arbitrary deleted basis plus X′) does not transfer directly to rank 5 at
  `N = 10`, and possibly not at `N = 15`.
* Decode the SAT models. Check whether they extend to matroids on `N + 5` elements (real
  counterexamples to X′₅), or only to local rank functions.
* Try stronger forms of the extension step:
  * choose `S` inside the Edmonds partition, rather than an arbitrary basis;
  * allow local re-orderings of `σ` near the insertion points;
  * use the density of `M \ S` inside the extension claim (tested above at `w = 7` only).
* KUM(5,10) itself: `kum_r_n.py 5 10` (still running at the time of writing).
