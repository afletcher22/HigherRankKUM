# Rank-4 extension theorem and a complete reduction of rank-4 KUM

Date: 2026-09-25.

Branch: `rank4-heavy-flat-splice-research` (continues `RANK4_HEAVY_FLAT_SPLICE.md`).

**Status.**

* §1–2: the **extension theorem**, SAT-certified and representation-free, with controls.
* §3: the divisible case `n=4k`, closed modulo the extension theorem and a 8-element SAT check.
* §4: the gcd-two case `n=4k+2`, including a paper proof of a new hitting lemma (Lemma H).
* §5: the resulting proof of rank-4 KUM, as a dependency graph with the status of each input.

Nothing here is Lean-certified yet. The SAT results were checked by several solvers and with
discriminating controls, but no proof certificates (DRAT/LRAT) have been produced or checked.
This note should be read as a **complete computer-assisted proof sketch that still needs
independent audit**, not as a settled theorem.

Scripts are in `experiments/rank4_heavy_flat_splice/` (README section "Extension theorem").
The SAT scripts need `python-sat`.

## 1. The extension theorem

Let `M` have rank 4, let `S` be a basis, and let `σ = (e_0, ..., e_{N-1})` be a CBO of `M\S`. An
**extension** of `σ` is a cyclic order of `E(M)` that is a CBO of `M` and whose restriction to
`E-S` is `σ` (same cyclic order). The elements of `S` may go into different gaps.

**Theorem X (local form).** Let `S` be a basis and `e_0, ..., e_13` further elements whose
4-windows `{e_i, ..., e_{i+3}}` are bases. Then `S` can be interleaved into the interior of the
sequence, with at least three `e`'s before the first and after the last element of `S`, so that
every 4-window of the merged sequence is a basis. The bound 14 is sharp.

**Theorem X' (extension theorem).** If `|E-S| >= 7`, every CBO of `M\S` extends to a CBO of `M`.
No density hypothesis is needed.

*Proof of X' from X.* If `N >= 14`, apply X to any 14 consecutive entries of `σ`.

* Every new window that contains an element of `S` lies inside the merged stretch.
* Every other window is 4 consecutive entries of `σ`, hence a basis.

For `7 <= N <= 13` use the cyclic SAT check of §2.2 for that `N`.

**Sharpness and the small cases.**

* The bound 14 in X is exact: binary survivors of length 13 exist (§2.3).
* X' fails at `N=6`. There are 10 binary deletion CBOs at n=10 with no extension (`ext_bin_exhaust.py 6`), all strict with profile `(2,4,7)` and **t=3**. One example: columns `[1,1,2,3,4,4,6,8,8,10]`, `S` one copy each of `1,2,4,8`, and `σ = [1,6,8,3,4,10]`.

**Relation to earlier notes.** Contiguous reinsertion of a basis can fail at every gap, and fails
even for light matroids (Conjecture U, `RANK4_HEAVY_FLAT_SPLICE.md` §9). Non-contiguous
reinsertion never fails once `N >= 7`.

* All 960 fully blocked orders at n=14 extend.
* All 13,776 fully blocked orders at n=18 extend (`ext_blocked.py`, `ext_blocked18.py`). Their
  shapes, by sizes of the runs of `S`: `2+1+1` 7,598 times, `3+1` 5,722 times, `1+1+1+1` 456
  times.

## 2. SAT certification of X and X'

### 2.1 Encoding (`local_sat.py`, `cyclic_sat.py`)

The variables are `r(X) >= v` for `v = 1..4`, for every subset `X` of every **block**
`S ∪ {e_i, ..., e_{i+5}}` (cyclic blocks in the cyclic case).

Inside each block the encoding imposes the matroid rank axioms:

* `r(∅)=0` and `r(X) <= |X|`;
* monotonicity and unit increase;
* local submodularity: if `r(X+a) = r(X+b) = r(X)` then `r(X+a+b) = r(X)`.

This is a **relaxation**: every rank-4 matroid satisfies it. The remaining clauses are:

* unit clauses saying `S` and the windows of `σ` are bases;
* for every admissible interleaving, one clause saying some window containing an element of `S`
  is not a basis.

Every such window is `T ∪ R` with `T ⊆ S` and `R` a run of at most 3 consecutive `e`'s, so it lies
in a block. **UNSAT therefore proves the claim for every matroid.**

`cyclic_sat.py N full` uses instead the full rank function on all `2^(N+4)` subsets. This is an
independent encoding.

### 2.2 Results

| Claim | Encoding | Size | Result |
|---|---|---|---|
| X, L=11, 12, 13 | blocks | up to 18,432 vars | **SAT** (expected, see §2.3) |
| X, L=14 | blocks | 20,480 vars, 488,752 clauses, 11,880 interleavings | **UNSAT**: CaDiCaL 2 s, Glucose4 2 s, MapleChrono 20 s |
| X, L=18 | blocks | 28,672 vars | UNSAT (6 s) |
| X' cyclic, N=6 | blocks | | **SAT** (the t=3 examples are genuine) |
| X' cyclic, N=7..14 | blocks | N=10: 20,224 vars, 17,160 interleavings | **UNSAT** for every N, CaDiCaL (at most 6 s each) |
| X' cyclic, N=8, 9, 10, 12 | blocks | | UNSAT also with Glucose4 and MapleChrono |
| X' cyclic, N=8 | full rank function | 16,384 vars, 462,977 clauses | UNSAT |
| X' cyclic, N=10 | full rank function | 65,536 vars, 2,360,675 clauses | UNSAT (16 s) |

### 2.3 Controls

* **Real counter-models are accepted.** Take the binary length-13 survivor
  `[1,2,5,8,3,4,9,2,12,1,6,8,2]`, together with the binary t=3 examples at `N=6`. With their true
  rank functions as assumptions, the `L=13` and `N=6` encodings are SAT
  (`local_sat_controls.py`, `cyclic_sat_controls.py`).
* **Real matroids satisfy the axiom part.** 40 random GF(3)/GF(5)/sparse-paving matroids with a
  CBO of `M\S` satisfy the axiom and window clauses of the `N=8` encoding, as do 20 random binary
  length-14 sequences for `L=14`.
* **The binary threshold is independently exact.**
  * `ext_local_bin.py` does a forward search over binary sequences (Y[0] up to the coordinate
    `S_4`), merging states. The surviving classes by length are 56, 672, 3840, 15158, 13926,
    18956, 22440, 31896, 17232, 12128, 4352, 2176, and 0 at length 14.
  * `ext_local_verify.py` is an independent brute-force interleaver. It confirms that all 2,176
    length-13 survivors have no interior interleaving, that all 17,408 of their length-14
    continuations have one, and that 3,000 random length-14 sequences have one.
* **The binary exhaustive cyclic check agrees** (`ext_bin_exhaust.py`, `S = {1,2,4,8}` WLOG):

  | Class | Non-extendable CBOs |
  |---|---|
  | all binary, n=14 | 0 (396,788 nodes) |
  | strict t=0, n=14 | 0 |
  | strict t=0, n=18 | 0 |
* **Adversarial real-matroid search** (`run_nonext_real.py`) covered GF(3), GF(5), GF(7) and
  sparse paving at `N=8, 9, 10`, over 250 matroids with a random basis. Every search space was
  exhausted and no non-extendable CBO was found.
* **Brute-force validation of the extension search** (`ext_crosscheck.py`): `ext.extend` agreed
  with brute-force enumeration of all CBOs on 75 random n=10 instances.

## 3. The divisible case `n = 4k`

**Theorem D.** Every uniformly dense rank-4 matroid on `4k` elements has a CBO.

*Proof.* Induction on `k`.

* `k=1` is trivial.
* `k=2` follows from `kum_small_sat.py 8`. It is UNSAT, so every uniformly dense rank-4 matroid on 8 elements has a CBO. The control without density is SAT.
* For `k >= 3`:
  * By Edmonds' covering theorem, `E` is the disjoint union of `k` bases.
  * Deleting one of them, `S`, leaves a union of `k-1` bases. That is uniformly dense on `4(k-1)`
    elements and of rank 4, so by induction it has a CBO.
  * Since `4k-4 >= 8`, X' extends it. ∎

This covers the strict branch that `docs/RANK4_COVERAGE.md` lists as open, and the non-strict
branch as well, without the tight-set machinery.

## 4. The gcd-two case `n = 4k+2`

Write `k-1/2 = (n-4)/4`. For a basis `S`, `M\S` is uniformly dense exactly when, for every
flat `F`, `|F - S| <= r(F)(k - 1/2)`. Since `S` is a basis, `E-S` automatically spans when planes
have fewer than `4k-2` elements.

In a strict t=0 matroid (points `<= k`, lines `<= 2k`, planes `<= 3k`) this means `S` must satisfy
the following:

| Flat | Required intersection with `S` |
|---|---|
| each `k`-point | at least 1 |
| each `2k`-line | at least 1 |
| each `3k`-plane | at least 2 |
| each `(3k-1)`-plane | at least 1 |

### Lemma H (hitting lemma, reduced case; paper proof)

Let `M` be strict with t=0 on `4k+2` elements, `k >= 2`, with **no 3k-plane and no 2k-line**.
Then `M` has a basis `S` with `M\S` uniformly dense.

*Proof.*

1. **At most one k-point.** Two k-points would span a line with at least `2k` elements.
2. **Complements of big planes.** Let `ℋ` be the set of `(3k-1)`-planes, and let `C_Π = E - Π`, of
   size `k+3`. For distinct `Π, Π'` in `ℋ`, `Π ∩ Π'` has rank at most 2, so it has at most `2k-1`
   elements. Then

   `|C_Π ∩ C_Π'| = |Π ∩ Π'| - 2k + 4 <= 3`.

   Hence every 4-set lies in at most one `C_Π`, and **a basis misses at most one plane of `ℋ`**.
3. **Start.** Take a basis `S` containing an element `p` of the k-point `P`, if there is one;
   otherwise take any basis. If `S` meets every plane of `ℋ` we are done. Otherwise `S ⊆ C_Π` for
   a unique `Π`, and `P ∩ Π = ∅`.
   * Let `I = S - p` (or `I = S` if there is no k-point), so `|I| >= 3`.
   * For `s` in `I`, let `X_s = Π - cl(S-s)`. It is nonempty: `cl(S-s)` is a plane other than `Π`, so
     `|Π ∩ cl(S-s)| <= 2k-1 < 3k-1`.
   * For `x` in `X_s`, `S_x = S - s + x` is a basis. It meets `Π`, and it contains `p`.
4. **When a swap can fail.** If `S_x ⊆ C_Π'`, then `S - s ⊆ C_Π ∩ C_Π'`. So `Π'` lies in
   `𝒬_s = {Π' in ℋ - Π : C_Π ∩ C_Π' = S - s}`. It therefore suffices to find `s` in `I` with `𝒬_s` empty.
5. **Three non-empty `𝒬_s` are impossible.** Suppose `s_1, s_2, s_3` in `I` and `Π_j` in `𝒬_{s_j}`.
   Let `R = C_Π - S`, so `|R| = k-1 >= 1`.
   * `Π_j ∩ C_Π = R ∪ {s_j}`, so `ℓ_j = Π_j ∩ Π` has exactly `2k-1` elements. It is therefore a line.
   * The three lines are distinct. If `ℓ_i = ℓ_j`, then for `r` in `R`, `cl(ℓ_i + r)` would be a
     plane equal to both `Π_i` and `Π_j`. But `s_i ∈ Π_i - Π_j`.
   * Points inside `Π` have at most `k-1` elements, because the only k-point avoids `Π`.
   * If the three lines share a point `q`, then `|ℓ_1 ∪ ℓ_2 ∪ ℓ_3| = 6k-3-2|q| >= 4k-1 > |Π|`.
   * Otherwise the triple intersection is empty, and the union has at least `6k-3-3(k-1) = 3k > |Π|`
     elements.

   Both cases are contradictions. ∎

`lemma_h.py` runs this construction on every adversarial starting basis, meaning every basis
through `p` that misses a `(3k-1)`-plane. It covered 36 reduced instances at k=3..6 over
GF(2)/GF(3)/GF(5), with 2,062 swap starts. Of these, 74 had one non-empty `𝒬_s` and 5 had two.
All 19,314 swaps were verified deletable, and every assertion held.

### Theorem T (strict t=0, `n=4k+2`)

Assume rank-4 KUM on `4k-2` elements. Then every strict t=0 rank-4 matroid on `4k+2 >= 14`
elements has a CBO.

*Proof.*

* With a 3k-plane, use Theorem G.
* With a 2k-line, use Theorem L4. Both are in `RANK4_HEAVY_FLAT_SPLICE.md`; they are paper
  proofs with SAT base lemmas, and they use no induction.
* Otherwise Lemma H gives `S` with `M\S` uniformly dense on `4k-2` elements. By hypothesis `M\S` has
  a CBO, and X' extends it, since `4k-2 >= 10`. ∎

## 5. Rank-4 KUM: the full argument

**Theorem.** Every uniformly dense rank-4 matroid has a cyclic basis ordering.

*Proof.* Induction on `n`.

| Case | Argument | Status of the input |
|---|---|---|
| `n` odd | van den Heuvel–Thomassé coprime theorem | external, published |
| `n=4k` | Theorem D (Edmonds + X' + n=8) | Edmonds external; X' and n=8 by SAT |
| `n=6`, `n=10` | `kum_small_sat.py 6`, `kum_4_10_sat.py` | SAT |
| `n=4k+2 >= 14`, proper tight set | `exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight` | **Lean**, needs rank-2 KUM at odd size `2k+1` (coprime theorem) |
| strict, t>0 | `exists_cbo_of_dangerous_hyperplane` | **Lean**, needs rank-3 KUM (vendored Rank3KUM, Lean) |
| strict, t=0, 3k-plane | Theorem G | paper (choice lemma, decomposition principle, Theorem 4 via Lean two-gap insertion) + SAT base lemma |
| strict, t=0, 2k-line | Theorem L4 | paper + SAT base lemmas |
| strict, t=0, otherwise | Lemma H + induction + X' | paper + SAT |

The induction is legitimate: every appeal is to KUM at `n-4`, for all uniformly dense rank-4
matroids of that size, whatever their class. ∎

**What changes in the programme.**

* **The divisible branch is now as easy as the coprime one.** No strictness analysis and no
  pair cycles are needed.
* **In the gcd-two branch, the only non-local work left is Theorems G and L4.** Random evidence
  suggests that even these can be replaced by a hitting lemma: all 960 heavy strict t=0 instances
  with 3k-planes and/or 2k-lines at k=3..6 have a deletable basis (`hit_general.py`, two seeds).
  A unified hitting lemma would give a proof using only X', Edmonds, vHT, the two Lean
  reductions and small SAT checks.
* **Superseded routes.** The following are no longer needed for rank 4:
  * elementary-lift completion;
  * pair-cycle orientation and repair;
  * contiguous-insertion selection rules (R1/R2);
  * the 14-element CEGAR base lemmas.

## 6. Caveats and next steps

1. **Certificates.**
   * Produce DRAT/LRAT proofs for `local_sat.py 14` and `cyclic_sat.py N` at N=7..13, and for
     `kum_small_sat.py 6, 8` and `kum_4_10_sat.py`.
   * Check them with a verified checker. For example, Lean's LRAT checker, used by `bv_decide`,
     would put X' inside the trusted Lean graph.
   * No C compiler was available in this session, so only multi-solver agreement was obtained.
2. **Human proof of Theorem X.** The UNSAT cores are small and fast (2 s), which suggests there is
   a readable case analysis.
3. **Unified hitting lemma**, removing the dependence on G and L4 (see §5).
4. **Independent audit** of Theorems G and L4. They now carry the heaviest informal load.
5. **Lean formalization** of Lemma H, Theorem D and the induction wrapper. These are short.
