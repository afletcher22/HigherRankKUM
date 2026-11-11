# Beyond rank 4: generic results, refuted shortcuts and candidate routes

Date: 2026-11-10. Branch: `probe/duality` (forked from `probe/rank4`).

**Status.** Section 1 is kernel-checked in Lean (standard axioms; probe workflow green on the
commit named there). Sections 2 to 6 are paper arguments and enumeration results; none of them
is formalized, and no claim there proves a new case of KUM. The enumeration scripts are in
`experiments/chains_of_bases/` (plain Python, no SAT solver; "exhaustive" always means over
binary matroids of the stated size).

Notation: `M` has rank `r` on `n` elements; `n = g·p`, `r = g·q` with `gcd(p, q) = 1`, so
`g = gcd(n, r)` and `p / q` is the density. A *CBO* is a cyclic basis ordering.

## 1. Formalized on this branch

| Result | Lean |
|---|---|
| Uniform density is self-dual; KUM at `(r, n)` iff KUM at `(n - r, n)` | `HigherRankKUM/Duality.lean` |
| KUM for every rank `r` and every `n ≤ r + 4` | `probes/Probe/Corank.lean` |
| Rank `r` reduces to strict matroids with `n ≥ 2r`, `gcd(r, n) > 1`; the tight reduction needs only the lower ranks divisible by `r / gcd(n, r)` | `HigherRankKUM/Skeleton.lean` |
| Block chains: `p` blocks of `g` elements, every `q` consecutive blocks a basis | `HigherRankKUM/VHT/BlockChain.lean` |
| Rank 5 reduces to strict `n = 5k`; rank 6 with `gcd(n, 6) ∈ {2, 3}` and a proper tight set | `probes/Probe/RankFiveSix.lean` |
| Fewer than `q` arcs of a vHT cover violate a given flat; a deletable basis exists if the proper heavy flats number fewer than `p / (q - 1)` | `HigherRankKUM/VHT/CoverAveraging.lean` |
| Heavy flats: `#heavy · (p + 1 - q·r) ≤ p · 2^r`; a deletable basis for every uniformly dense matroid with `n ≥ r · 2^(r+1)` (no strictness) | `HigherRankKUM/VHT/HeavyFlats.lean` |
| At a fixed density, KUM at the multiple `g` follows from the strict cases at multiples `2..g`; `gcd(n, r) = 2` with a proper tight set, in every rank | `HigherRankKUM/RatioInduction.lean` |
| Aligned window criterion for interleavings (the reinsertion step of Section 4) | `HigherRankKUM/SlotInsertion.lean` |

All rows except the last built clean on the full probe list at commit `d834c99`;
`SlotInsertion.lean` built clean on its own at commit `1850171`.

Limit of the large-`n` deletion theorem: with an extension theorem it would reduce KUM at size
`n` to size `n - r`, but the descent stops just below `r · 2^(r+1)`, where nothing is known. New
cases need deletion at small sizes or a different induction.

## 2. One object: twisted chains

A **twisted chain** of rank `g` is a cyclic sequence of `g`-sets `X_1, …, X_m` and matroids
`N_1, …, N_m` of rank `g` such that `X_i` and `X_{i+1}` are bases of `N_i`. It **closes** if every
`X_i` can be ordered so that `X_i → X_{i+1}` is a serial exchange in `N_i`: every suffix of `X_i`
with the complementary prefix of `X_{i+1}` is a basis of `N_i`. Each relation is total on both
sides (greedy augmentation), so the only obstruction is closing the cycle (*holonomy*).

Instances:

* **Coherent chains** (`N_i = M` for all `i`): `k` disjoint bases in a cyclic order. A closed
  coherent chain of an Edmonds partition is a CBO; so divisible KUM is the statement that some
  coherent chain closes. For `k = 2` this is Gabow's conjecture for that pair.
* **Block chains** (Section 1): `N_y = M / (F_{y+1} ∪ … ∪ F_{y+q-1})`, the chain runs through
  the blocks with step `q`. For `g = 2` this is the pair-cycle theory of Sprints 2 to 5.
* The two cycles of Section 3 and the chain of Section 4.

For representable matroids let `A_i` express `X_{i+1}` in the basis `X_i` (in `N_i`). A minor of
`A_i` on rows `T`, columns `T'` is nonzero iff `(X_i - T) ∪ T'` is a basis, and `X_i → X_{i+1}`
is serial for given orders iff all leading principal minors are nonzero (an LU factorization
without pivoting). In a coherent chain `∏ A_i = I`. In general `H = ∏ A_i` is a holonomy matrix;
for `g = 2` an unorientable chain has `H` with zero diagonal.

## 3. Two-block refinement

**Split lemma (Greene–Magnanti; Wiedemann for sequences).** For bases `B = D ⊔ T` and `S` there
is a partition `S = X ⊔ Y` with `D ∪ X` and `T ∪ Y` bases. Hence for any cyclic sequence of
bases `B_1, …, B_k`, any `c` and any `T_1 ⊆ B_1` of size `c`, there are `T_i ⊆ B_i` with
`(B_i - T_i) ∪ T_{i+1}` a basis for all `i`: start from a symmetric exchange for two bases and
insert the others one at a time between `D_i` and `T_{i+1}`, which is again a basis. For
representable matroids this is Cauchy–Binet applied to `∏ A_i = I`.

**Decoupling.** With `B_i = T_i ⊔ D_i` as above (sizes `c` and `r - c`), a full ordering exists
with every `T_i` leading iff two twisted chains close: the `T`-chain (`N_i = M / D_i`, rank `c`)
and the `D`-chain (`N_i = M / T_{i+1}`, rank `r - c`). The orders of the `T`'s and of the `D`'s do
not interact. Rank 4 with `c = 2` gives two pair cycles (XP for `m` even). Rank 5 with `c = 3`
gives a pair cycle and a triple cycle.

**Triples.** For triangles `A`, `B` in a rank-3 matroid, `(f, m, ℓ) → (f', m', ℓ')` is serial
iff `A - f + f'` and `B - ℓ' + ℓ` are bases: firsts are related by the exchange graph, lasts by
the reverse exchange graph, and the only coupling is `f ≠ ℓ`. Each graph misses at most two
edges at a vertex. A fully rigid triple cycle (every triple elementwise parallel to the next)
closes iff its holonomy permutation is the identity. One non-rigid relation is **not** enough to
close a cycle: an inscribed triangle sends every first element anywhere except to its own point.
So the slack/tight dichotomy of XP has no direct rank-3 analogue.

## 4. Rank induction by one element per block

Every window of a CBO on `r·k` elements contains exactly one element from the positions
`0, r, 2r, …`. Conversely:

1. Pick `x_0`. `M / x_0` contains `k` disjoint bases: Edmonds' condition
   `|A| ≤ k·r'(A) + k - 1` follows from uniform density of `M`. Let `Y` be their union and `X`
   the `k` other elements (`x_0 ∈ X`).
2. `Q = (M / x_0) | Y` is uniformly dense of rank `r - 1`; a CBO `σ` of `Q` has every window
   together with `x_0` a basis of `M`.
3. Put the elements of `X` at the `k` equally spaced slots of `σ`. No window contains two of
   them, so `x` fits a slot iff it is independent of the `r` windows around it. Reinsertion is a
   bipartite matching between `X` and the slots, and `x_0` fits every slot
   (`exists_cyclicBasisOrder_of_aligned_windows` with `s = 1`).

Without step 2's universality this is exact: KUM at `(r, r·k)` holds iff for some `X` the
twisted chain of rank `r - 1` with `N_i = M / x_i` closes.

Evidence (`schemeR.py`, `schemeR5.py`): R10 works from all 90 choices of `(x_0, x_1)`, with
1,440 of 10,980 orderings of `Q` extending. On strict binary matroids the share of sampled
orderings of `Q` that extend is

| bases | rank 4 | rank 5 |
|---|---|---|
| 2 | 58.6% | 41.7% |
| 3 | 24.2% | 16.3% |
| 4 | 13.0% | 7.4% |

and every one of the 64 matroids had choices of `X` that work. The share falls by a roughly
constant factor per basis (`0.417^2 = 0.174`, `0.417^3 = 0.073` in rank 5). So an arbitrary
ordering of `Q` is not enough: the induction hypothesis has to supply an ordering adapted to
`X`, that is, a statement about the twisted chain. The gain is that rank 5 would rest on rank 4
(fully proved) instead of on its own 10-element case, and the first step is a 10-element
statement: `n = 2r` from `n = 2(r - 1)`, one element and one slot.

## 5. What vHT returns near the uniform weights

Theorem 2.1 gives an arc placement for every rational point `w` of the base polytope. If every
point of the circle is covered by a basis, every arc ends where another begins, so the arcs form
*necklaces*; a necklace with `m` elements has integer total length. For generic `w` there is one
necklace winding `r` times. Near the uniform point its elements fall into `g` virtual tracks,
and the order in which the tracks advance at a block is the order of partial sums of the
perturbation. Because the tracks shift by one after a full turn, that order cannot be constant:
for `g = 2` a single necklace has an **odd** number of *twists* (a block that enters in one
order and leaves in the other), and two necklaces have an even number; a CBO is two necklaces
and no twist. In an all-tight chain the threading is forced to follow parallelism and every tick
order is valid, so an all-tight odd chain is a valid placement for **every** weight near the
uniform point. The rigid chains are the placements that survive perturbation; CBOs are not.
Perturbing the weights therefore cannot produce a CBO, which is the structural reason Theorem
2.1 stops at the coprime case.

## 6. Refuted or closed

* **One-point insertion into a fixed CBO of `M \ e`**: fails for R10 (every `e`, all 768
  orderings), although R10 has 288 CBOs.
* **Injective vHT** ("if `ω(A) ≤ D·r(A)` and `|E| ≤ D` then the starting points can be
  distinct"): false. Rank 2, `D = 4`, parallel pairs with weights `(2, 2)` and `(3, 1)`: the
  first pair starts at `0` and `2` up to rotation, and the second pair then starts at two points
  of which one is `0` or `2`.
* **Prefix freedom** (any subset of a basis can lead its ordering): true for two bases in every
  case tested, false for three bases in rank 5. A failure is one blocked split of one basis.
* **Prescribed initial segments on both of two bases**: false (8% of symmetric-exchange pairs
  in rank 5).
* **Window invariants span.** For matroids representable in characteristic 0, uniform density is
  GIT semistability of the point configuration, the tight reduction is the passage to the
  polystable point, and a CBO for the order `σ` exists iff the product `P_σ` of the cyclic
  window determinants is nonzero (the point lies in the open positroid cell for `σ`). KUM says
  the `P_σ` have no common zero on the semistable locus. They span all invariants of
  multidegree `(r, …, r)` for `r = 2` and `(r, n) = (4, 6)`, but not for `(3, 6)` (35 of 40) or
  `(3, 7)` (205 of 225), and `(3, 7)` is coprime. So spanning is not the mechanism.

## 7. Targets, in order

1. The two-base step of Section 4 from rank 4 to rank 5: a Kotlar–Ziv type statement for the
   pair `(M / x_0, M / x_1)` on 8 elements. It would give a human proof of KUM(5, 10).
2. `gcd(n, r) = 2` in even rank beyond 4: the tight half is done; the strict half needs a
   deletable basis at small sizes, an insertion lemma for `q` pairs, and the sizes
   `2r ≤ n < 3r`.
3. A closing criterion for triple cycles (Section 3), needed by rank 5 for more than two bases
   and by rank 6 with `gcd = 3`.
4. Minimal uniformly dense matroids (a CBO of a matroid with fewer bases is a CBO of `M`; in
   rank 2 the minimal ones have at most three parallel classes). Untested beyond rank 2.
