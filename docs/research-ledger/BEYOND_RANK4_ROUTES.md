# Beyond rank 4: generic results, refuted shortcuts and candidate routes

Date: 2026-11-10. Branch: `probe/duality` (forked from `probe/rank4`).

**Status.** Section 1 is kernel-checked in Lean (standard axioms; probe workflow green on the
commit named there). Sections 2 to 6 and 8 are paper arguments and enumeration results; none of
them is formalized, and no claim there proves a new case of KUM. Section 8 was added on
2026-11-11. The enumeration scripts are in
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

All rows built clean on the full probe list at commit `f1fd0c5`.

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

### Refinement trees: rank 5 without triple cycles

Sections 3 and 4 are the same operation at different block sizes: split every block of a
twisted chain into two, which leaves two twisted chains of smaller rank. A CBO is a full binary
refinement tree whose leaves are single elements. Only the root split is coherent, hence free
(the split lemma); every deeper split is a closing problem in a twisted chain, and a pair at a
leaf is a pair cycle.

* The two-base case of Section 4 is not a new statement: peeling the first column of two bases
  is the first step of a serial symmetric exchange, so `n = 2r` from `n = 2(r - 1)` is Gabow's
  problem for some complementary pair. The route differs from basis insertion only for three or
  more bases.
* Rank 5 can use the tree `5 = 1 + (2 + 2)` instead of `5 = 3 + 2`: the root split `(4, 1)` is
  free; the 4-blocks `W_i` form a twisted chain with `N_i = M / x_i`; splitting them into pairs
  needs a closed walk of 2-subsets with `Q_{i-1} ∪ P_i` a basis of `M / x_i` (six states per
  block); the leaves are two pair cycles. No triple cycle occurs. In a fully rigid chain the
  split closes iff the holonomy permutation of four points fixes some pair setwise, so the
  obstructions are 3-cycles and 4-cycles.
* For representable matroids the matrix of the chain after peeling `x_i`, `x_{i+1}` is the Schur
  complement of that entry of `A_i`, so the holonomy of a peeled chain is a product of
  compressions of matrices whose product is the identity. A closed walk of `c`-subsets exists as
  soon as the `c`-th compound of the holonomy has a nonzero diagonal entry.

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

1. The tree `1 + (2 + 2)` for rank 5 (Section 8). Three pieces, in order: (a) prove the slack
   lemma for all matroids (it is a statement about two relations on six states); (b) show that
   strict density excludes a pair-split cycle whose composite is tight with the identity
   blocked, at least for one root split of every chain; (c) the leaves: the two pair cycles,
   which fail for 0.01% to 0.3% of the root splits of strict matroids.
2. `gcd(n, r) = 2` in even rank beyond 4: the tight half is done; the strict half needs a
   deletable basis at small sizes, an insertion lemma for `q` pairs, and the sizes
   `2r ≤ n < 3r`.
3. KUM(5, 10) by hand. In the language of Section 4 it is a Kotlar–Ziv type statement for the
   pair `(M / x_0, M / x_1)` on 8 elements, that is, Gabow's problem in rank 5 for some
   complementary pair; in this repository it is known only by SAT.
4. A closing criterion for triple cycles (Section 3), needed by rank 6 with `gcd = 3`.
5. Minimal uniformly dense matroids (a CBO of a matroid with fewer bases is a CBO of `M`; in
   rank 2 the minimal ones have at most three parallel classes). Untested beyond rank 2.

## 8. The tree `1 + (2 + 2)`: the pair split of 4-blocks

Scripts: `pairsplit_local.py`, `pairsplit_chain.py`, `pairsplit_adv.py`, `pairsplit_two.py`,
`pairsplit_rigid_example.py`; numbers in `pairsplit_result.txt`.

**Setting.** `B_0, …, B_{k-1}` are disjoint bases of a rank-5 matroid in a cyclic order. A
*root split* picks `x_i ∈ B_i` with `B_i - x_i + x_{i+1}` a basis (a closed walk in the exchange
graphs; always exists). Put `W_i = B_i - x_i`. A *pair split* picks a trailing pair
`Q_i ⊆ W_i` for every `i`, with `Q_i ∪ x_{i+1} ∪ (W_{i+1} - Q_{i+1})` a basis. So it is a closed
walk through the relations

    T_i(Q, Q') = 1  iff  Q ∪ x_{i+1} ∪ (W_{i+1} - Q')  is a basis,

each on the six 2-subsets of a 4-set. If it closes, what is left are two pair cycles.

### Local theory: one relation

Let `W`, `W'` be bases of a rank-4 matroid `N` and `T(Q, Q') = [Q ∪ (W' - Q') is a basis]`.

* `T` is a permutation of the six states iff `W'` is elementwise parallel to `W` (*rigid*).
  Proof: a row with one entry means two elements of `W'` lie in the closure of `Q`; an element
  of `W'` lies in the closure of three pairs if it is parallel to an element of `W`, of one pair
  if its fundamental circuit has two elements of `W`, and of none otherwise; `6 · 2 = 4 · 3`.
* For a bijection `π : W → W'` say `T` *meets* `π` if `Q ∪ π(W - Q)` is a basis for some `Q`.
  `T` is **slack** if it meets all 24 bijections and **tight** otherwise: some bijection `β` has
  `Q ∪ β(W - Q)` dependent for all six `Q`. For a matrix `A` of `W'` in the basis `W`, tight
  means that after a column permutation all six principal `2 × 2` minors vanish:
  `a_ii a_jj = a_ij a_ji`. A rigid relation with parallel map `π` blocks `β` exactly when
  `π⁻¹β` is a 3-cycle or a 4-cycle.
* Types up to relabelling `W` and `W'`: 51 over `F_2` (17 tight), 434 over `F_3` (31 tight;
  one new dense tight type, a symmetric Hadamard matrix), both exhaustive. Adding 6,000,000
  sampled matrices over each of `F_5` and `F_7` gives 1,664 types, 36 of them tight. Every tight
  type contains a bijection (`Q ∪ π(W - Q)` a basis for all `Q`); 41 slack types contain none.
* For matrices over one field the set of relations is closed under composition after a field
  extension: `T(A D B) = T(A) ∘ T(B)` for a generic diagonal `D`, because the monomials
  `d_k d_l` of the 2-compound of `D` are distinct. The 1,664 types are closed under composition.

### Closing criterion (verified, not proved)

* **Slack lemma.** A cycle that contains one slack relation closes. Checked for every cycle
  with relations of the `F_2` types, of the `F_3` types, and of the 1,664 types (the semigroups
  of products have 948, 1,305 and 1,664 classes). No proof for arbitrary matroids yet.
* A cycle fails iff its composite relation is tight with the identity blocked. For a rigid
  chain this is the holonomy 3-cycle or 4-cycle of Section 4.
* A full row or column is not needed: only 1 of the 51 binary types meets every permutation of
  the six states, but 34 are slack.

### Two bases: an identity

Take `B_0` as the unit vectors, `B_1` as the columns of `A`, `x_0` = row 0, `x_1` = column 0. A
split of size `c` closes iff some `c`-subsets `Q`, `Q'` of the other indices have
`det A[Q, Q'] ≠ 0` and `det A⁻¹[Q', Q] ≠ 0` (Jacobi). By Cauchy–Binet

    Σ_{Q'} det A[Q, Q'] · det A⁻¹[Q', Q]  =  1 - Σ_{i ∈ Q} A[i, 0] · A⁻¹[0, i],

because the compression of `A · A⁻¹` to the other indices is the identity minus a rank-one
matrix. So the split closes unless `A[i, 0] · A⁻¹[0, i] = 1 / c` for every `i ≥ 1`. When the
characteristic divides `c` this is impossible: **for two bases of a binary matroid of rank 5
every choice of `x_0`, `x_1` admits a pair split**, with no assumption on the root split.
`pairsplit_two.py` found no failure over `F_3` (227,548 matrices) or `F_5` (192,593) either. The
shape matters: the split `(1, 1, 3)` over `F_2` and `(1, 1, 2)` in rank 4 over `F_3` do fail.
For `k` bases the holonomy is the identity minus a matrix of rank at most `k - 1`, and the
identity no longer decides it.

### Measurements

Share of valid root splits, binary matroids of rank 5:

| source | `k` | root splits | some relation slack | pair split closes | 4-blocks close completely |
|---|---|---|---|---|---|
| strict, random | 2 | 79,396 | 98.9% | all | 99.7% |
| strict, random | 3 | 87,610 | 97.5% | all | 99.93% |
| strict, random | 4 | 15,342 | 98.2% | all | 99.99% |
| `M(K_6)` | 3 | 6,624 | 97.5% | all | 99.92% |
| sparse random chains, no density assumption | 2 | 39,366 | 72.6% | all | 97.4% |
| sparse random chains | 3 | 61,788 | 94.8% | all | 99.7% |
| sparse random chains | 4 | 24,390 | 98.4% | all | 99.98% |

Every chain in every run had a root split that closes completely. Compare Section 4, where a
fixed ordering of the contraction extends in 42% / 16% / 7% of cases: fixing only the single
elements `x_i` and leaving the 4-blocks free loses almost nothing, and the loss shrinks as `k`
grows.

**The pair split can fail.** `pairsplit_rigid_example.py`: three bases over `F_2` with all
three relations rigid and holonomy a 3-cycle; that root split does not close (16 of the 17
root splits of the chain do, 12 completely). The matroid is not strict: a hyperplane holds 12
of its 15 elements. No strict example and no random example has been found.

### What this changes

* The split step is governed by a small finite object (six states; 36 tight types found),
  and a single non-degenerate relation settles it. This is the analogue of the slack/tight
  dichotomy of XP that triples do not have (Section 3).
* The remaining obstructions are of two kinds: cycles of tight relations whose composite blocks
  the identity, and failing pair cycles at the leaves. Both are rare and both come from
  parallel structure in contractions, which is what strict density limits. A proof for rank 5
  along this tree would be a density argument against these two configurations for one root
  split per chain, not a search.
