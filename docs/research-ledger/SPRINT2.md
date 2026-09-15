# Sprint 2 — gcd-two pair-orientation obstruction

**Start date:** 2026-09-15 (America/Phoenix)

**Branch:** `rank4-research-sprint2`

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

After orienting each pair, aligned rank-`2h` windows are bases by admissibility.  The shifted window from block `i` is

`{last(P_i)} ∪ C_i ∪ {first(P_{i+h})}`,

where `C_i = P_{i+1} ∪ ... ∪ P_{i+h-1}`.

## Evidence status at sprint start

### Abstract candidate

**Claim:** for a cyclic family of Boolean relations with full support in both coordinates, unsatisfiability occurs iff every relation is a bijection and their composition around the cycle has no fixed point.

**Initial status:** checked by direct finite case analysis outside Lean; formal proof pending.

A useful proof route is: composition of full-support relations remains full-support; any nonfunctional full-support factor forces the total composition to be nonfunctional; a full-support functional relation on a two-point set is a bijection. Therefore a fixed-point-free total composition can occur only when every local relation is a bijection.

### Recovered historical search

File Library artifact: `rank4_binary_pair_cycle_exact.py` (2026-08-06).

The script enumerates **actual binary vector-matroid pair cycles**, not abstract Boolean patterns.  Vectors are nonzero elements of `GF(2)^4`; repeated vector values in nonadjacent blocks represent distinct parallel ground elements.  Admissibility is exactly that adjacent pair-unions are bases, which is the rank-four specialization `N=m`, `h=2`.

The orientation relation in the script is exactly the shifted four-window relation between `P_i` and `P_{i+2}` through middle block `P_{i+1}`.

The historical definitions are:

- **one break:** merge one adjacent pair of pair blocks into an arbitrary ordered four-element chunk; all other pair blocks remain contiguous but freely oriented;
- **distance-two double break:** do this simultaneously to two disjoint adjacent-pair chunks separated by two block edges, disturbing four consecutive pair blocks.

The large counts are still treated as historical computational evidence; they have not been rerun in this sprint.

### Certified small obstruction

A small independent verifier has been preserved at `experiments/sprint2_pair_obstruction_certificate.py`.

Pair blocks over `GF(2)^4`:

`(1,2), (4,8), (1,14), (4,7), (6,9)`.

Independent checks performed before committing the verifier:

- ambient labelled vector matroid has rank 4 on 10 elements;
- all five adjacent pair-unions are bases;
- local orientation relations are equality, equality, equality, inequality, equality;
- hence the forced parity is odd and all `2^5 = 32` fixed-pair orientations fail;
- two independent GF(2) rank implementations agree on every subset;
- all 1022 nonempty proper subsets satisfy `2|A| < 5 r(A)`.

Thus this witness is **strictly uniformly dense** and lies in the intended residual frontier.  It is a counterexample to universal orientability of a fixed admissible pair cycle, not to KUM.

## Computation budget

Do not rerun the historical `m=5,7,9` enumeration.  Sprint computation is limited to exact verification of the single ten-element witness and, if needed, tiny finite checks of the abstract two-point relation theorem.  No random search and no repair search.

## Formalization target

1. An abstract two-state cyclic relation theorem, independent of matroids.
2. A matroid local-compatibility lemma: `C_i` independent, contraction rank two, both endpoint pairs bases, and the endpoint compatibility relation has full support.
3. A fixed-pair-cycle obstruction theorem connecting these local relations to orientability.  If cyclic-index/reindex infrastructure becomes disproportionate, isolate that exact gap rather than weakening hypotheses silently.

## Current decision

Proceed with the forced-transition characterization.  The certified strict binary witness shows the obstruction is mathematically real and relevant; the next question is structural, not whether such fixed-cycle obstructions exist.
