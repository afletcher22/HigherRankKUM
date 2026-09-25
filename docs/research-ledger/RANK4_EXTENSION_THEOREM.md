# Rank-4 extension theorem and a complete reduction of rank-4 KUM

Date: 2026-09-25.

Branch: `rank4-heavy-flat-splice-research` (continues `RANK4_HEAVY_FLAT_SPLICE.md`).

**Status.**

* §1–2: the **extension theorem**, SAT-certified and representation-free, with controls.
* §3: the divisible case `n=4k`, closed modulo the extension theorem and a 8-element SAT check.
* §4: the gcd-two case `n=4k+2`. A basis whose deletion keeps uniform density always exists in the
  strict t=0 case. This is Lemma U (paper, `k >= 4`, via double covers), and SAT with Lemma H at
  `k = 3`. Theorems G and L4 are no longer needed.
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

### 2.4 Independent re-implementation (`indep_check/`)

A separate agent wrote new code for Claims X (linear) and X' (cyclic), working only from the
mathematical statement and without seeing the scripts above. It used two encodings:

* **E1 (exact, no relaxation).** One variable per subset of size 1–4, with hereditary clauses and
  single-step augmentation. Its models are exactly the rank-4 matroids, so its SAT models are
  genuine counterexamples and its UNSAT answers are direct proofs.
* **E2 (block relaxation).** Blocks are `S ∪ {4 consecutive e's}`, narrower than the 6 used above.

Its interleaving enumeration comes from two independent generators, which agree with each other
and with the closed formula (11,880 at L=14 and 17,160 at N=10).

| Instance | E1 exact | E2 blocks |
|---|---|---|
| linear, L=12 | SAT | SAT |
| linear, L=13 | SAT | SAT |
| linear, L=14 | **UNSAT** (CaDiCaL 43 s, Glucose 34 s) | UNSAT |
| cyclic, N=6 | SAT | SAT |
| cyclic, N=7 | UNSAT | UNSAT |
| cyclic, N=8 | UNSAT | UNSAT |
| cyclic, N=10 | UNSAT | UNSAT |
| cyclic, N=12 | UNSAT | UNSAT |

These match §2.2 in every case.

**Controls of the re-implementation** (`controls.py`, `verify.py`):

* The E1 SAT models at N=6, L=12 and L=13 were re-verified as genuine matroids by brute force over
  the whole power set, and none of their interleavings works.
* The binary N=6 counterexample satisfies both encodings.
* Nine random GF(2)/GF(3)/GF(5) matroids on 18 elements violate no axiom clause.
* `U_{4,18}` violates exactly the 11,880 interleaving clauses.
* Three kinds of non-matroid are rejected: one violating augmentation, one violating heredity,
  and one violating submodularity.

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

### Lemma U (unified hitting lemma, `k >= 4`; paper proof)

Let `M` be strict with t=0 on `4k+2` elements, `k >= 4`. Then `M` has a basis `S` with `M\S`
uniformly dense. No assumption about 3k-planes or 2k-lines is made. In fact **every double
cover** of `M` contains such a basis.

**Double covers.** Double every element. The doubled matroid has `4(2k+1)` elements and is
uniformly dense at the integral ratio `2k+1`. By Edmonds it splits into `2k+1` bases. Two copies
of an element are parallel, so they lie in different bases. The result is a family
`B_1, ..., B_{2k+1}` of bases of `M` in which every element lies in exactly two.

**Demand flats and victims.** The demand flats are the flats in the table above, with demand
`d(F)`. Say `B_i` is a *victim* of `F` if `|B_i ∩ F| < d(F)`. The *deficit* of `F` is

`δ(F) = Σ_i (r(F) - |B_i ∩ F|) = (2k+1) r(F) - 2|F|`.

| Flat | `δ(F)` | Deficit at a victim |
|---|---|---|
| k-point | 1 | 1 |
| 2k-line | 2 | 2 |
| 3k-plane | 3 | at least 2 |
| (3k-1)-plane | 5 | 3 |

So **every demand flat has at most one victim.** A k-point's non-victims each meet it exactly once,
so the point is a *vertex* `cl(b)` of each of them. A 2k-line's non-victims each meet it in exactly
two elements, so the line is an *edge* `cl(b, b')` of each of them.

A plane `F` has `|B ∩ F| = 3` iff `F = cl(B - b)` for some `b ∈ B`, that is, iff `F` is a *face* of
`B`. A basis has exactly 4 faces.

*Proof.* Suppose every `B_i` is a victim. Choose, for each `i`, a demand flat `F_i` with victim `B_i`.
These `2k+1` flats are distinct. Let `p`, `l` and `m = m_K + m_H` count the k-points, 2k-lines, and
3k- or (3k-1)-planes among them.

1. **Basic bounds.** `p <= 4`, since `5k > 4k+2`.
   * **(C1)** No point of the family lies in a line or (3k-1)-plane of the family.
   * **(C2)** No line of the family lies in a (3k-1)-plane of the family.

   In each case the bigger flat's victim would also be the smaller flat's victim.
2. **Lines of the family are pairwise disjoint, so `l <= 2`.**
   * If two of them met, they would span a plane with at least `3k` elements. That plane is then a
     3k-plane `L ∪ L'`, and `L ∩ L'` is a k-point `P`.
   * Every other basis meets both lines in 2 and the plane in at most 3, so it meets `P`.
   * The two victims miss `P`. Hence `2|P| = 2k-1`, which is impossible.
3. **`p >= 3` is impossible.**
   * Three k-points span the 3k-plane `K = P_1 ∪ P_2 ∪ P_3`. The `2k-2` bases that are not their
     victims have the form `{p_1, p_2, p_3, c}` with `c ∉ K`.
   * Any flat inside `K` that meets some `P_i` contains it. From this one checks that none of these
     bases misses a 2k-line or a (3k-1)-plane, or meets a 3k-plane `K' ≠ K` in at most one element:
     `K ∩ K'` is a line with at least `2k-2 > k` elements, hence contains two `P_i`.
   * So they can only be victims of a k-point inside `E - K`. There is at most one such k-point,
     because `|E - K| = k+2 < 2k`.
4. **Deficit budget.** Let `R` be the total deficit of the family's planes at bases other than their
   own victims. The table gives `R <= m_K + 2 m_H <= 2m`.
   Each basis `B` has at most 4 faces. So at least `m - 4` of the family's planes (`m - 5` if `B`'s
   own flat is a plane) have deficit at least 1 at `B`. Hence

   `(p + l)(m - 4)⁺ + m(m - 5)⁺ <= R <= 2m`.
5. **`k >= 5`.** Here `m = 2k+1-p-l >= 2k-3 >= 7`. For `m >= 8`, `m(m-5) > 2m`. For `m = 7`, we
   have `k = 5` and `p+l = 4`, so the left side is `26 > 14`.
6. **`k = 4`.** Here `m >= 5`.
   * `m >= 7` fails as in step 5 (`m=7` gives `20 > 14`).
   * **`m = 6`** has `p + l = 3`, so `l >= 1`, and the budget is tight (`12 = 12`). Tightness forces
     every plane of the family to be a (3k-1)-plane, and every face of every basis to be one of
     them. The family's line `L` is an edge of its 8 non-victims, so `L` lies in two of their faces.
     These faces are (3k-1)-planes of the family, which contradicts (C2).
   * **`m = 5`** forces `p = l = 2`. The two lines are disjoint and cover `4k` elements. By (C1) the
     k-points avoid both lines, but only 2 elements remain.

   All cases are contradictions. ∎

**Consequence.** For `k >= 4` the strict t=0 case needs neither Theorem G nor Theorem L4, nor
Lemma H.

**Checks.**

* `double_cover.py` builds random double covers by matroid partition (shortest augmenting paths).
  It checked 7,518 covers of random and structured strict t=0 instances at k=3..6. Every cover
  contained a deletable basis, every demand flat had at most one victim, and victim-distinct
  2k-lines were always disjoint.
* `hit_structured.py` ran about 9,700 structured instances at k=3,4,5: stars of 2k-lines through a
  k-point, several k-points, and 3k-planes through a common point or line. All had deletable
  bases. They had up to 20 demand flats at k=3 and 14 at k=4,5, so a crude count of flats would not
  suffice; the victim argument is needed.

### k = 3 (n = 14): SAT plus Lemma H

The counting does not reach `k=3`. The hitting lemma there is checked representation-free by
`hit_sat14.py`:

* the full rank function on all `2^14` subsets, with the rank axioms, no loops, and the strict t=0
  caps (points <= 3, lines <= 6, planes <= 9);
* one clause per 4-set `B`, saying that `B` is not a basis, or that `E-B` contains a 3-set of rank
  1, a 6-set of rank at most 2, or an 8-set of rank at most 3.

The unsplit formula is hard for the solvers, so it is split by the flat that Lemma H does not cover
(`hit_sat14_split.py`):

| Case | Result |
|---|---|
| elements 0..8 form a 9-plane | **UNSAT** (CaDiCaL, 439 s) |
| elements 0..5 form a 6-line, and there is no 9-plane | **UNSAT** (48 s) |
| no 9-plane and no 6-line | Lemma H (paper, valid for `k >= 2`) |

So **the hitting lemma holds for every `k >= 3`**: by Lemma U for `k >= 4`, and by SAT with Lemma H
for `k = 3`.

**Controls.**

* The first version of the encoding omitted the no-loop clauses and returned a spurious model with
  two loops. That model was caught when the flats were decoded, and the clauses were added.
* `hit_sat14_control.py` relaxes the caps to allow t>0 or tight lines. Any model is then re-checked
  independently of the encoding: submodularity, uniform density, and a direct scan of all 1,001
  4-sets for a deletable basis.

### Theorem T (strict t=0, `n=4k+2`)

Assume rank-4 KUM on `4k-2` elements. Then every strict t=0 rank-4 matroid on `4k+2 >= 14`
elements has a CBO.

*Proof.* The hitting lemma (Lemma U for `k >= 4`; SAT with Lemma H for `k = 3`) gives a basis `S`
with `M\S` uniformly dense on `4k-2` elements. By hypothesis `M\S` has a CBO, and X' extends it,
since `4k-2 >= 10`. ∎

Theorems G and L4 (`RANK4_HEAVY_FLAT_SPLICE.md`) are no longer used. They remain an independent
second proof of the 3k-plane and 2k-line cases.

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
| strict, t=0, `k >= 4` | Lemma U + induction + X' | paper (Lemma U) + SAT (X') |
| strict, t=0, `k = 3` | hitting lemma (SAT split + Lemma H) + KUM(10) + X' | paper + SAT |

The induction is legitimate: every appeal is to KUM at `n-4`, for all uniformly dense rank-4
matroids of that size, whatever their class. ∎

**What changes in the programme.**

* **The divisible branch is now as easy as the coprime one.** No strictness analysis and no
  pair cycles are needed.
* **The gcd-two branch needs only the hitting lemma.** The proof now uses only:
  * X' (SAT);
  * Edmonds and van den Heuvel–Thomassé;
  * the two Lean reductions (tight sets, dangerous hyperplanes);
  * Lemma U and Lemma H (short paper proofs);
  * small SAT checks: KUM at n=6, 8, 10 and the n=14 hitting split.

  The decomposition principle, the base lemmas and Theorems G and L4 are no longer on the critical
  path.
* **Superseded routes.** The following are no longer needed for rank 4:
  * elementary-lift completion;
  * pair-cycle orientation and repair;
  * contiguous-insertion selection rules (R1/R2);
  * the 14-element CEGAR base lemmas.

## 6. Caveats and next steps

1. **Certificates.**
   * Produce DRAT/LRAT proofs for `local_sat.py 14`, `cyclic_sat.py N` at N=8, 10, 12,
     `kum_small_sat.py 6, 8`, `kum_4_10_sat.py`, and the two cases of `hit_sat14_split.py`. These
     are the only SAT claims the proof uses.
   * Check them with a verified checker. For example, Lean's LRAT checker, used by `bv_decide`,
     would put X' inside the trusted Lean graph.
   * No C compiler was available in this session, so only multi-solver agreement was obtained.
2. **Human proof of Theorem X.** The UNSAT cores are small and fast (2 s), which suggests there is
   a readable case analysis.
3. **Independent audit of Lemma U and Lemma H.** These are the only informal proofs left on the
   critical path, and both are short.
4. **Lean formalization** of Lemma U, Lemma H, Theorem D and the induction wrapper. The double
   cover needs Edmonds' covering theorem, and the `n=14` hitting split needs a SAT certificate
   like the others.
