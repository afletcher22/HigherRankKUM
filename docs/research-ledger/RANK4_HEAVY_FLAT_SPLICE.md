# Rank-4 heavy-flat splice and 3k-plane completion audit

Date: 2026-09-24.

Branch: `rank4-heavy-flat-splice-research`, based on
`rank4-t0-elementary-lift-reformulation` at `42a1f62`.

**Status.**

* §1: checked informal derivation. It is not Lean-certified. Its only nontrivial input is the
  Lean-proved `Rank3KUM.TwoGap.universalTwoGapInsertion` in the vendored Rank3KUM snapshot.
* §2 and §3: refutations, with exact certificates.
* §4: remarks and a conjecture.
* §5: computational evidence.
* §7 (added later the same day): the decomposition principle and **Theorem G**. It is proved
  by paper argument plus a SAT-certified 10-element base lemma, and it supersedes the
  threshold-based use of Corollary 6.

No claim here proves rank-4 KUM.

Scripts: `experiments/rank4_heavy_flat_splice/`, described in the README in that folder.

Notation: `M` has rank 4 and ground set `E`, with `n=|E|`. A *window* is 4 cyclically
consecutive entries of an order. The *slack* of a flat `F` of rank `rho` is
`s(F) = rho*n/4 - |F|`. Uniform density means that every slack is `>= 0`.

## 1. Heavy-flat splice (HFS)

### Lemma 1 (window decomposition)
Let `F` be a flat of rank `rho`, and let `W` be a 4-set with `|W∩F| = rho`. Then `W` is a basis
of `M` iff `W∩F` is independent and `W-F` is a basis of `M/F`.

*Proof.* If `W∩F` is independent then `cl(W∩F)=F`, so `r(W) = rho + r_{M/F}(W-F)`. If `W∩F` is
dependent then `r(W) <= 3`.

### Lemma 2 (rank-2 single-gap splice)
In a matroid of rank 2, let `{a,b}` and `{s,t}` be bases with `a,b,s,t` distinct. Then one of the
orders `(s,t)` or `(t,s)`, written `(first, second)`, has `{a,first}` and `{second,b}` both bases.

*Proof.* Bases are exactly pairs of nonloops in different parallel classes. If both orders
failed, then `a` would be parallel to `b`, or `s` parallel to `t`.

### Lemma 3 (Rank3KUM, Lean)
Let the matroid have rank 3, let `D` be a basis, and let `p,a,b,c,q ∉ D` be distinct with
`{p,a,b}`, `{a,b,c}` and `{b,c,q}` all bases. Then `D` can be inserted contiguously at the gap
`a|b` or at the gap `b|c`.

The statement is purely local and assumes no density.

### Theorem 4 (heavy-flat local splice)
Let `F` be a flat of rank `rho` in {1,2,3}. Let `B` be a basis of `M` such that `B∩F` is a basis
of `F`. Let `σ'` be a CBO of `M\B`.

Suppose `σ'` contains an **F-site**:

* rho=3: 7 consecutive entries with F-pattern `1011101` (written `w u x1 x2 x3 v y`);
* rho=1: 7 consecutive entries with F-pattern `0100010` (written `w p x1 x2 x3 p' y`);
* rho=2: 6 consecutive entries with F-pattern `100110`, `011001`, `010101` or `101010`.

Then `M` has a CBO. It is obtained by inserting `B` inside the site, and it again contains an F-site.

*Proof.*

* **rho=3.** Apply Lemma 3 in `M|F` with `D = B∩F` and `(p,a,b,c,q) = (w,x1,x2,x3,y)`.
  * The three hypotheses come from the windows `{w,u,x1,x2}`, `{x1,x2,x3,v}` and `{x2,x3,v,y}`
    via Lemma 1.
  * Let `c` be the element of `B-F`. Replace `x1 x2 x3` by `x1 d0 d1 c d2 x2 x3` for the first gap,
    or by `x1 x2 d0 c d1 d2 x3` for the second gap.
  * Each new window then consists of three F-elements and one outside element. Its F-triple is one
    certified by Lemma 3, is `B∩F`, or is an old triple, so the window is a basis by Lemma 1.
* **rho=1.** Use the same argument with Lemma 3 applied in `M/F`.
  * `B-F` is inserted into the non-F order.
  * The element of `B∩F` is placed so that parallel elements stay exactly 4 apart.
* **rho=2.** Take the case `l2 x1 x2 | l3 l4 x3` and insert `l'a l'b z'a z'b` at the bar.
  * `(l'a,l'b)` comes from Lemma 2 in `M|F` at the pair `(l2,l3)`.
  * `(z'a,z'b)` comes from Lemma 2 in `M/F` at the pair `(x2,x3)`.
  * The pairs `{l2,l3}`, `{x1,x2}`, `{x2,x3}` and `{l3,l4}` are certified by the old windows
    `{l2,x1,x2,l3}` and `{x2,l3,l4,x3}`.
  * Each of the seven new windows is an F-pair from the F-order together with a non-F pair from
    the non-F order, and each such pair is certified.
  * The patterns `011001`, `010101` and `101010` are handled the same way.

### Lemma 5 (forced sites)
Let `N=n-4` and `m=|F-B|`. Every window of `σ'` contains at most `rho` elements of `F`.

Every CBO of `M\B` has an F-site if one of the following holds:

* **rho=3:** `3m > 2N`. In fact there are at least `3m-2N` sites.
  * Let the gaps `g` be the numbers of F-elements between consecutive non-F entries. Then `g<=3`.
  * A gap of 3 is a site unless it is adjacent to a gap of 0.
  * Counting with the gap counts `a_j` gives `#sites >= a_3 - 2a_0 >= m-2(N-m)`.
* **rho=1:** `5m > N`.
  * Parallel elements are at least 4 apart, so every gap is at least 3.
  * The number of gaps different from 3 is at most `N-4m`.
* **rho=2:** `16m > 7N`.
  * At most `2N-4m` windows contain fewer than 2 F-elements.
  * Four consecutive regular windows force a 4-periodic 7-entry stretch, and each of the six
    possible stretches contains a site.

Thresholds for `n=4k+2`:

| Flat | Heavy when | Examples |
|---|---|---|
| plane | `|Π| > (8k+5)/3` | 3k-planes for k≥6; dangerous planes for k≥3 |
| point | `|P| > (4k+3)/5` | k-points for k≥4 |
| line | `|L| > (28k+18)/16` | 2k-lines for k≥5 |

Thresholds for `n=4k`: planes `> (8k+1)/3`, points `> (4k+1)/5`, lines `> (28k+4)/16`.

The defect count `4*s(F)` explains the constant defects recorded elsewhere in the ledger:

* the six-window count of a 3k-plane (`s=3/2`);
* the three-defect count of a balanced 3k hyperplane in `M\e` (`s=3/4`);
* the constant-seven count of a saturated `3k-1` set in `M\e` (`s=7/4`).

A tight flat (`s=0`) is regular everywhere, which recovers tight-set gluing.

### Corollary 6 (heavy-flat reduction)
Suppose `M` has a heavy flat `F` and a **hitting basis** `B ⊇` basis of `F` such that `M\B` is
uniformly dense. Then any CBO of `M\B` yields a CBO of `M`. The CBO of `M\B` can come from
induction on `k` and may lie in any class.

Consequently, rank-4 KUM on `4k+2` (and likewise on `4k`) reduces to three open parts:

* (i) **light** matroids, meaning that no flat meets its threshold;
* (ii) the hitting lemma;
* (iii) small `k`, where the thresholds do not yet apply.

In particular, the endpoints (a) and (b) of the elementary-lift dichotomy are both 3k-planes.
For k≥6 they are covered by Corollary 6, provided the hitting lemma holds. So the six-defect
selector and the completion-from-σ problem are no longer needed in that range.

## 2. Refuted: 3k-plane completion from an arbitrary deletion CBO

This refutes the target in `RANK4_T0_ELEMENTARY_LIFT_REFORMULATION.md` §12–14. It covers
"no CCC-good cut => pair-completion" and, more generally, any completion that keeps the inherited
cyclic K-order.

* **Binary, k=3** (`verify_fail1.py`)
  * Columns `(4,1,3,6,6,3,2,5,7,13,9,13,9,13)`, with `K` = labels 0..8 and `e=11`.
  * Deletion CBO `σ=(0,10,2,6,13,3,1,12,7,5,9,8,4)`, of type 1+1+1. Its inherited K-order is a
    *perfect* rank-3 CBO of `K`.
  * Exhaustive enumeration: 826,176 CBOs of `M` (with label 0 first) give 4,080 induced K-orders,
    and the inherited order is not among them.
* **GF(3), k=3** (`verify_fail2.py`)
  * `e=12`, `σ=(0,13,3,11,2,8,6,10,5,1,9,7,4)`, of type 2+1, again with a perfect inherited order.
  * 1,383,360 CBOs give 4,144 induced K-orders, and the inherited order is not among them.
* **k=4** (`k4_mech.py`)
  * 3 failures in 168 targeted cases, each confirmed by exhaustive DFS over placements of the
    complement.

**Mechanism.** The complement `C=E-K` has rank 2: two parallel classes on one line meeting `K`
at a point `p`.

* Every window containing two complement elements needs the cross pair, together with a
  consecutive K-pair taken from different lines through `p`.
* In the inherited order such good pairs are isolated.
* So each cross adjacency absorbs at most 1 of the 6 defect units, and there are at most 4 cross
  adjacencies.
* With `r(C)=2` the CCC branch is unavailable as well.

At k=2 every labelled case completes: 153,232 cases, independently reproduced by
`run_c_n10.py`. So the failure first appears at k=3.

## 3. Refuted: perfect-core 3k-plane gluing

* **Instance:** n=10 binary, columns `[6,7,10,11,12,13,14,14,15,15]`.
  * `H={6,7,10,11,12,13}` is the Fano plane minus a point, i.e. `M(K4)`.
  * The complement is two parallel pairs on the line through the missing point.
* **Result:** none of the 16 rank-3 CBOs of `H` extends to a CBO of `M`. Every one of the 2,496
  CBOs of `M` (with label 0 first) induces 1 or 2 bad H-triples (`orbit8.py`, `orbit8b.py`).
* **Reason:** every rank-3 CBO of `M(K4)` puts opposite edges next to each other.

This gives an explicit witness for the previously unrecorded claim that a fixed perfect-core
six-defect selector fails.

## 4. Remarks

* **(a) and (b) are one object.** A saturated unbalanced line of `N` and a balanced 3k plane of
  `D` are both simply a 3k-point plane of `M`. Deleting any element outside the plane turns
  case (a) into case (b).
* **The two-minor basis-path lemma (§13) is correct as stated.**
  * In the application, `(M/P)|C` is automatically loopless, because `cl(P) ⊆ K`.
  * It has rank 2 exactly when `P` is C-good.
  * The lemma requires `r(C)>=3`; when `r(C)=4`, apply it to the rank-3 truncation.
* **Conjecture (evidence only).** If `r(C)>=3`, every rank-3 CBO of `K` extends.
  * This held on all 72 exact n=10 planes with `r(C)>=3`, and on every sampled k=3,4 instance
    (`run_g_rank.py`).
  * All observed failures have `r(C)=2`.
  * Switching to another 3k-plane does not avoid `r(C)=2` (`run_switch.py`).

## 5. Computational evidence

| Check | Script | Result |
|---|---|---|
| exact n=10 strict t=0 binary class | `orbits.py 10 2` | 28,476 patterns, 16 GL(4,2) orbits, exact orbit-stabilizer check |
| completion keeping inherited K-order, k=2 | `run_c_n10.py` | 153,232 cases, all complete |
| plane splice (Theorem 4, rho=3) | `bsl.py`, `run_bsl.py` | 493 splices at k=3..6, all verified CBOs |
| point and line splice (rho=1,2) | `hfs.py`, `run_hfs.py` | 187 point and 143 line splices at k=3..6, all verified |
| hitting lemma for heavy flats | `hitting.py`, `run_hit.py` | 193 heavy instances at k=4..10, all have a hitting basis |
| contiguous basis splice, light matroids | `run_light.py` | 230 random-basis splices, 0 blocked |

The fields are GF(2), GF(3) and GF(5) unless stated otherwise. The samples are seeded and are
not exhaustive.

### Earlier basis-splice induction session (summary)
An earlier independent session tested rank-4 basis-splice induction: delete a
density-preserving basis `D` and reinsert it contiguously. The two exhaustive search scripts are
included in `experiments/rank4_heavy_flat_splice/bsi/`. Its findings, not re-run here:

* **Fully blocked orders exist.** Binary t=0 matroids have fully blocked `(D,σ)` pairs with
  `D = {1,2,4,8}`: 960 orders from 48 matroids at n=14, and 13,776 orders from 360 matroids at n=18.
  Explicit n=14 witness: columns `[1,1,2,2,4,4,7,8,9,9,10,11,12,13]`, `D` one copy each of
  `1,2,4,8`, and blocked σ (as values) `[1,10,4,9,11,7,13,9,2,12]`.
* **A universal basis always existed.** At binary n=10, 14 and 18, every blocked matroid still had
  a density-preserving `D` that splices into *every* CBO of `M\D`.
* **The hitting lemma fails at k=2.** A density-preserving basis can fail to exist; the failures
  have type (2,4,6) with five doubled points.

## 6. Remaining gaps, in order of leverage

1. **Light class** (no heavy flat) together with **small k**. This is the only non-local gap. The
   k=7 growing-distance witness (profile (6,12,20)) is light.
   * Proposed static target: for a suitably generic basis `B` and every CBO `σ'` of `M\B`, if all
     24 contiguous insertions of `B` fail at every gap, then `M` has a heavy flat.
   * Falsify first by adapting `bsi/block_exhaust.py` to light matroids at n=22 and 26.
2. **Hitting lemma** for Corollary 6. This is a finite covering problem, analogous to Rank3KUM's
   near-tight hitting basis lemma.
3. **Lean formalization** of Theorem 4, Lemma 5 and Corollary 6. These are short, and they reuse
   the vendored two-gap theorem.

**Retire:**

* completion from an arbitrary deletion CBO;
* perfect-core and fixed-selector six-defect gluing;
* the (a)/(b) distinction as a separate endpoint.

References: van den Heuvel–Thomassé, arXiv:0912.2929; McGuinness, *Cyclic orderings of paving
matroids*, arXiv:2308.12239. McGuinness uses the same delete-a-basis / universal-reinsertion
architecture, with paving playing the role of lightness.


## 7. Decomposition principle and Theorem G (3k-planes, all k)

### Observation
Theorem 4 needs only three things:

* a CBO of `M\B` that contains an F-site;
* `B∩F`, a basis of `F`;
* `B`, a basis of `M`.

It needs no density, hitting or threshold hypothesis, and its output again contains an F-site.
So sites propagate, and the counting in Lemma 5 is needed only to start the chain.

### Decomposition principle (DP, checked informal)
Suppose the following hold:

* `F = F0 ∪ T1 ∪ ... ∪ Tm` with each `Ti` a basis of `M|F`;
* `Z1,...,Zm` are disjoint sets outside `F` such that each `Bi = Ti ∪ Zi` is a basis of `M`;
* `M0 = M \ (B1 ∪ ... ∪ Bm)` has a CBO containing an `F0`-site.

Then `M` has a CBO: apply Theorem 4 `m` times, reusing the site each time.

The slack of `F` does not change along the chain. Consequently a flat of slack `s` has a base
of fixed size, independent of `k`. For example:

* a 3k-plane has a 10-element base with `|F0|=6`;
* a k-point has a 10-element base with `|F0|=2`;
* a 2k-line has a 10-element base with `|F0|=4`.

### Base lemma (SAT-certified, representation-free)
Every uniformly dense rank-4 matroid on 10 elements with a 6-point plane `K0` has a CBO
containing a K0-site.

The encoding is in `base_sat.py`:

* the rank function on all 1,024 subsets, in order encoding;
* rank axioms (monotone, unit increase, local submodularity);
* density;
* flatness of `K0`;
* one clause for each of the 51,840 candidate site sequences.

The problem is UNSAT for each of `r(C)=2,3,4`, where `C` is the complement.

Controls (`base_sat_sanity.py`, `base_sat_controls.py`):

* the core clauses alone are SAT, and the model they give is a matroid;
* the orbit-8 matroid satisfies the core clauses;
* restricting to the skeleton S1 gives SAT for `r(C)=3` (as expected) and UNSAT for `r(C)=2`;
* restricting to S2 gives SAT for `r(C)=2`.

The case `r(C)=2` is proved independently by `b2_exhaustive.py`. That script enumerates all 20
loopless rank-3 matroids on 6 elements (points <=2, lines <=5) and all 423 admissible
partitions by planes through `cl(C)`, and finds an S1 ordering in every case.

### Choice lemma (paper proof)
Let `M` be strict with t=0 on `4k+2` elements, `k >= 3`, and let `K` be a 3k-plane with
`C=E-K`. Partition `K` into `k` bases `D_i` (Edmonds). Then there are two of them, `D_a` and
`D_b`, and a set `C0 ⊆ C` with `|C0|=4`, such that `M0 = M|(D_a ∪ D_b ∪ C0)` is uniformly dense.

*Proof.* Uniform density of `M0` means: at most 2 elements per point, at most 5 per line and at
most 7 per plane. We split on the rank of `C`.

* **`r(C)=4`.** Take `C0` to be a basis of `M` inside `C`, and any `D_a,D_b`.
* **`r(C)=3`.** Let `ℓ = cl(C)∩K`. Density gives `|ℓ| <= 3k-(k+2) = 2k-2`, so some `D_a` has at
  most 1 element on `ℓ`, and `D_b` can be any other basis. Take `C0` of rank 3 with at most 2
  elements per point. The only plane that can contain `C0` is `cl(C)`, and it meets
  `D_a ∪ D_b` in at most 3 elements.
* **`r(C)=2`.** Let `L = cl(C)` and `P = L∩K`, so that `|P| <= k-2`.
  * The planes through `L` meet `K` in lines `ℓ_Π ⊇ P`, each with `|ℓ_Π| <= 2k-2`.
  * The requirements are `|P∩K0| <= 1` and `|ℓ_Π∩K0| <= 3` for every such plane.
  * A basis `D` avoiding `P` has 2 elements on at most one `ℓ_Π`. Call that plane its heavy
    plane.
  * If two bases that avoid `P` have different heavy planes (or none), use them.
  * Otherwise every basis avoiding `P` has 2 elements on the same line `ℓ*`. Counting then gives
    `|P| >= 2`.
  * The bases meeting `P` contain at most `|P|-2` elements of `ℓ*` outside `P`. So some basis
    meeting `P` has none, and pairing it with a basis that avoids `P` works.

### Theorem G (paper + SAT)
Every strict rank-4 matroid with t=0 on `4k+2` elements (`k >= 2`) that has a rank-3 flat with
`3k` elements has a CBO.

*Proof.*

* For `k=2`, apply the base lemma to `M` itself.
* For `k >= 3`, the choice lemma gives the base, the base lemma gives it a site-CBO, and DP
  (with `T_i` the remaining bases `D_i` and `Z_i` the remaining elements of `C`) builds the
  CBO of `M`.

This closes both elementary-lift endpoints (a) and (b) for **all** k. It uses no deletion CBO,
repair argument, hitting lemma or `k` threshold. It also covers:

* the exact binary n=10 class, since every orbit has a 6-plane;
* the historical n=18 witness;
* the growing-distance witnesses k=3,4,5;
* the completion counterexamples of §2.

End-to-end pipeline check (`theorem_g.py`, `run_theorem_g.py`): 202 instances at k=2..7 over
GF(2)/GF(3)/GF(5), all producing verified CBOs. Every case of the choice lemma occurred except
the "basis meeting `P`" sub-case.

### Other flats (`base_sat_general.py RHO F`)

| Flat | Base (`|F0|`, n0=10) | Base lemma | Choice lemma |
|---|---|---|---|
| dangerous plane (3k+1) | 7 | UNSAT: holds | not needed (t>0 already solved) |
| 3k-plane | 6 | UNSAT: holds | proved above |
| k-point | 2 | UNSAT: holds | evidence only (`theorem_pl.py`: 36 instances, k=3..6) |
| 2k-line | 4 | UNSAT: holds | evidence only (36 instances, k=3..6) |
| (3k-1)-plane | 5 | **SAT: fails at n0=10** | needs a 14-element base |
| (2k-1)-line | 3 | **SAT: fails at n0=10** | needs a 14-element base |

### Updated frontier for strict t=0, `4k+2`
The following are now covered:

* a 3k-plane, by Theorem G;
* a k-point or a 2k-line, once their choice lemmas are written up.

What remains is matroids with **points <= k-1, lines <= 2k-1, planes <= 3k-1**. The k=7
growing-distance witness (profile (6,12,20)) lies there, as the boundary case of a
(3k-1)-plane.

Next steps:

1. Paper proofs of the point and line choice lemmas.
2. 14-element base lemmas for (3k-1)-planes, (2k-1)-lines and (k-1)-points. This probably
   needs SAT with lazy (CEGAR) site clauses.
3. The remaining light class.


## 8. Other heavy flats, the n=10 case, and the two regimes

### 8.1 Choice lemmas as density conditions
A basis `B` of `M` with `B∩F` a basis of `F` is exactly a basis of the direct sum
`N_F = M|F ⊕ M/F`. So DP only needs a 10-element set `E0` such that:

* `M|E0` is uniformly dense, plus the extra base conditions below;
* `N_F|(E-E0)` is uniformly dense at the integral ratio `k-2`. By Edmonds this makes it split
  into `k-2` bases of `N_F`.

### 8.2 Minimal extra base conditions (SAT, `base_sat_minimal.py`)

| Base flat | Extra condition on the 10-element base |
|---|---|
| 6-plane | none |
| 7-plane | none |
| 2-point | none |
| 4-line | none |
| 5-plane | holds exactly under **no 7-plane and no 5-line** (fails with either condition alone) |
| 3-line | holds under **no 7-plane** alone (fails with "no 5-line" alone) |

The two failures of §7 at `n0=10` therefore come only from non-strict bases.

### 8.3 Theorem L4 (2k-lines; paper + SAT)
Every strict rank-4 matroid with t=0 on `4k+2` elements that has a line with `2k` elements has a
CBO.

*Proof.* If `M` has a 3k-plane, Theorem G applies. Otherwise every class of `M/L` has at most
`k-1` elements. For `k=2` the base is `M` itself. For `k>=3`, choose `L0 ⊆ L` with `|L0|=4`
and `X0 ⊆ X=E-L` with `|X0|=6` satisfying:

* (L-a) each point `p` of `L`: `|p|-(k-2) <= |p∩L0| <= 2`;
* (X-a) each `M/L`-class `Q`: `|Q|-(k-2) <= |Q∩X0| <= 3`;
* (X-b) each point of `M` inside `X` has at most 2 elements in `X0`;
* (X-c) `r(X0) >= 3`;
* (LX) if `r(X0)=3`, then `cl(X0)` contains at most one element of `L0`.

These conditions give uniform density of `M|E0`:

* A line coplanar with `L` has at most 2+3 elements of `E0`.
* A skew line misses at least one element of `X0`.
* A plane through `L` has at most 4+3 elements of `E0`.
* Any other plane has at most 2 elements of `L0`, and it contains all of `X0` only if it
  equals `cl(X0)`; then (LX) applies.

They also give the `N_L` partition: each point of `L` and each class of `X` retains at most
half of the remainder.

Existence:

* **Capacities.** The capacities `min(3, Σ_q min(2,|q|))` over classes sum to at least 6,
  because there are at least 3 classes, and 2 big classes force at least 4 singleton classes.
* **Collinear `X0`.** If `X0` lies on a skew line, one swap fixes it. A skew line meets each
  class in at most one point, and the elements that are sole representatives of heavy classes
  number at most 4, which is less than 6.
* **(LX) fails.** Then `cl(X0)` meets `L` in a k-point, and density gives `X ⊄ cl(X0)`.
  Replacing a non-coloop, non-essential `y ∈ X0` by some `x ∉ cl(X0)` makes `r(X0)=4`. This
  needs the facts that `X0` has at most 1 coloop and that `x`'s point is disjoint from `X0`.
* **`L0`.** It then exists: the requirements sum to at most 4 and the capacities to at least 4.

### 8.4 Rank-4 KUM on 10 elements (SAT)
The encoding forbids all 181,440 cyclic orders.

* `kum_4_10_sat.py strict` is UNSAT (192 s): every strict rank-4 matroid with t=0 on 10
  elements has a CBO.
* `kum_4_10_sat.py`, with no strictness, is UNSAT (519 s): **every uniformly dense rank-4
  matroid on 10 elements has a CBO**. This is a direct, representation-free computer proof that
  depends on no other result.

The result also follows from the base lemmas plus McGuinness: a matroid either has a parallel
pair (point lemma), or has a line with at least 3 points (line lemmas), or is paving.
Non-strict cases on 10 elements follow from tight gluing, and t>0 from the dangerous-core
constructions. So **rank-4 KUM holds for all 10-element matroids**; `(4,10)` was the smallest
open parameter in the Sprint 0 coverage table.

### 8.5 The two regimes
DP needs a flat of bounded slack, since the base size grows linearly with the slack. After
Theorems G and L4, and the point, 5-plane and 3-line cases (choice lemmas under test in
`choice_general.py`), the uncovered strict t=0 class is **points <= k-1, lines <= 2k-2,
planes <= 3k-2**.

* Base lemmas at 14 elements would shift this to points <= k-2, lines <= 2k-4,
  planes <= 3k-5. No fixed ladder of base sizes can cover every matroid.
* The other extreme, paving matroids, is McGuinness's theorem. McGuinness proves it with
  basis deletion and universal contiguous reinsertion.

**Key question:** does universal (or suitably chosen) contiguous basis reinsertion hold once
every flat has slack at least some **constant** `s0`, independent of `k`? If it does, finitely
many base lemmas (up to size about `(4/3)(s0+5)`) together with such a light-regime theorem
would close strict rank-4 KUM.


## 9. The light regime: universal reinsertion for every basis is false

### 9.1 Conjecture U and its exact refutation
**Conjecture U.** Let `M` be light: strict, t=0, points <= k-1, lines <= 2k-2,
planes <= 3k-2. Then every basis `B` inserts contiguously into every CBO of `M\B`. For light `M`,
`M\B` is automatically uniformly dense.

**Evidence for U:**

* `run_light_block.py` ran an exhaustive DFS for fully blocked orders on light GF(3)/GF(5)
  matroids with the most degenerate bases sampled. It covered 36 cases at k=4 and 24 at k=5 and
  found **0 blocked orders**.
* Both blocked examples of the earlier basis-splice session are heavy.

**Exact binary test** (`run_U_binary.py`). For binary matroids the standard basis is WLOG, and
`bsi/block_exhaust.py` lists every fully blocked `(M, D={1,2,4,8}, σ')`.

* n=14: 48 blocked matroids, **all heavy** (each has a (2k-1)-line and a plane of size at
  least 3k-1). U holds exactly for binary n=14.
* n=18: 360 blocked matroids; 348 are heavy and **12 are light**, all with profile
  `(3,6,10)`. **U is false.** Example: columns
  `(1,1,2,2,3,3,4,4,5,5,8,8,9,10,12,15,15,15)`.

### 9.2 Which basis fails (`run_U_basis_rule.py`, exact)
In each of the 12 light blocked matroids there are 131 basis types and exactly **one** is not
universal: `{1,2,4,8}`.

* Every element of that basis has a parallel mate. This does not characterize it: 276 universal
  basis types have the same property.
* The distinguishing feature is that `15 = 1+2+4+8` is the unique parallel class of size
  `k-1 = 3`. The bad basis is exactly the one that misses it, with `15` in general position with
  respect to it.

**Refined target (Conjecture U\*, evidence only).** In a light matroid, a basis meeting every
parallel class of size `k-1` inserts universally.

Caveats:

* All 12 counterexamples to U belong to one structural family, so this evidence is thin.
* For small `k` there can be more than four classes of size `k-1`, so the selection rule may have
  to be weakened. For example, it could hit near-tight flats in the sense of Rank3KUM's
  hitting-basis lemma.

**Consequence for the programme.** Once the three pending choice lemmas are proved, strict t=0
rank-4 KUM on `4k+2` reduces to **one** selection-plus-insertion theorem for light matroids. This
is the rank-4 analogue of Rank3KUM's "near-tight hitting basis + two-gap insertion". On the
paving side, McGuinness's argument uses paving only in circuit elimination between two 4-circuits.
In general matroids that step gains one extra alternative, which arises only from small circuits
through pairs of `B`-elements (§8.5 key question).

### 9.3 Choice lemmas: evidence
`run_choice_general.py` searches for a 10-element base with the required density and strictness
and then runs the full construction. It gave **159/159 successes** for k-points, 2k-lines,
(2k-1)-lines and (3k-1)-planes at k=3,4,5 over GF(2)/GF(3)/GF(5), with the base lemma never
failing.


## 10. Session wrap-up (selection rules, cascade gaps, 14-element bases)

### 10.1 Anatomy of the light counterexamples to U (`analyze_light_block.py`)
Take the binary n=18 example with the blocked basis `B={1,2,4,8}`. The blocked order
`σ' = [1,10,4,3,15,5,2,9,15,3,8,5,15,12]` has this structure:

* The three copies of `15` sit 4 apart. Each has full support on `B`: its fundamental circuit
  uses all of `B`.
* Every other element has support at most 2, meaning it lies on one of the six lines spanned by
  pairs of `B`.
* Every gap is flanked by low-support elements, so all 24 orders fail.

In a paving matroid every element outside `B` has support at least 3, so this mechanism cannot
occur. That is why McGuinness's insertion works there.

### 10.2 Tetrahedral family search (`tetra_family.py`)
The instances are light, with `B = e1..e4`, most other elements on the pair-lines of `B`, and a
full-support point of multiplicity `k-1`.

| Field, k | Instances | Blocked |
|---|---|---|
| GF(2), k=4 | 12 | 1 |
| GF(2), k=5 | 12 | 1 (2 searches hit the node budget) |
| GF(3), k=4 | 12 | 0 |
| GF(3), k=5 | 12 | 0 |

For every blocked instance, exactly one of 131 basis types fails. Both candidate selection rules
are consistent with the data:

* **R1:** the basis meets every parallel class of size `k-1`.
* **R2:** the basis minimises the number of elements on its pair-lines. The bad basis has 11
  (k=4) or 14 (k=5) such elements, against a minimum of 6.

### 10.3 Gaps in the 10-element cascade
The choice lemmas for (3k-1)-planes and (2k-1)-lines cannot always be met with a 10-element base.

* **(3k-1)-plane, k>=5.** If the complement (`k+3` elements) is collinear, every base contains 5
  collinear points, which violates the "no 5-line" condition.
* **(2k-1)-line.** If the complement of the line lies in a single plane, which density allows at
  k>=5, every base contains 7 coplanar points.

Such configurations need 14-element base lemmas, or a different flat of the same matroid.

### 10.4 14-element base lemmas by lazy SAT (`base_cegar.py`)
This is SAT with lazily generated clauses (counterexample-guided refinement).

1. Solve over rank functions.
2. Extract a candidate matroid.
3. Run an exhaustive site-anchored search for a site-CBO.
4. If one is found, forbid it, together with random relabellings inside `F0` and `X0`.
5. If none exists, report a genuine counterexample.

**Validation (`cegar_check10.py`).** It reproduces the three known 10-element results: holds after
about 216 learned orders, the counterexample, and holds under strictness after about 496.

**The 14-element run.** The case was an 8-point plane in a base strict at level 3 (points <=3,
lines <=6, planes <=9). The run was stopped after about 3.6 h and about 5,400 learned orders,
with **no counterexample** but no proof either; iterations had slowed to about 13 s each. This
is inconclusive. Better engineering (symmetry breaking, stronger learned clauses, a faster site
search) is needed to finish it.

### 10.5 Status at wrap-up
**Proved (paper + SAT):**

* Theorem G (3k-planes);
* Theorem L4 (2k-lines);
* rank-4 KUM on 10 elements.

**Strong evidence (159/159 pipelines):**

* k-points;
* (2k-1)-lines and (3k-1)-planes, except for the configurations in §10.3.

**Open:**

* paper choice lemmas for k-points, (2k-1)-lines and (3k-1)-planes;
* 14-element base lemmas for the configurations in §10.3;
* the light regime, where a selection rule (R1 or R2) plus universal insertion is the target.
  "Every basis" is false (§9).


## 11. Superseded by the extension theorem (2026-09-25)

See `RANK4_EXTENSION_THEOREM.md`. Contiguous reinsertion (§9–10) is the wrong target:
**non-contiguous** reinsertion of a basis into a CBO of `M\S` always succeeds once
`|E-S| >= 7`, in every rank-4 matroid (SAT-certified). This gives:

* the divisible case `n=4k` outright, via Edmonds;
* the strict t=0 gcd-two case, via Theorems G and L4 of this note together with a new hitting
  lemma (Lemma H).

The open items of §10.5 are therefore no longer needed:

* the choice lemmas for k-points, (2k-1)-lines and (3k-1)-planes;
* the 14-element base lemmas;
* the light-regime selection rules.
