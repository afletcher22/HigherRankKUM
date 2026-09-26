# Reducing the SAT content of the rank-4 proof

Date: 2026-09-26.

The kernel-checked rank-4 proof on branch `probe/rank4` uses these certificates:

* KUM(4,6) and KUM(4,8);
* X′ on 8, 10 and 12 elements, and X on 14 elements;
* five 10-element certificates for KUM(4,10);
* `hit14line` and `hit14g` (the hitting lemma at `k = 3`).

This note records which of them can be replaced by human proofs.

## KUM(4,6): replaced

`HigherRankKUM.Rank4.exists_cyclicBasisOrder_of_rank_four_six`, in the main library, proves it by
duality with rank-2 KUM. `Probe/Rank4/Full.lean` now uses it instead of the certificate.

## KUM(4,8): published human proof

With `n = 2r`, Edmonds splits a uniformly dense matroid into two disjoint bases `B`, `C`. A full
serial symmetric exchange `b₁…b_r`, `c₁…c_r` makes the cyclic order `b₁ … b_r c₁ … c_r` a cyclic
basis ordering: every window is `B − {b₁..bᵢ} + {c₁..cᵢ}` or `C − {c₁..cᵢ} + {b₁..bᵢ}`.

* Kotlar and Ziv, *On serial symmetric exchanges of matroid bases*, J. Graph Theory (2012),
  arXiv:1110.1826. Any two disjoint bases of a rank-4 matroid have a full serial symmetric
  exchange (Theorem 4.1, about 3 pages on top of Sections 2–3).
* Kotlar, *On circuits and serial symmetric basis-exchange in matroids*, SIAM J. Discrete Math.
  27 (2013), arXiv:1110.5166. In rank 5 it gives only an exchange of length at most 6, which is
  not enough for KUM(5,10).
* KUM(5,10) itself holds: `kum_r_n.py 5 10` is UNSAT, taking 4337 s.

## KUM(4,10): a new route with no 10-element certificates

The five certificates split strict t=0 KUM(4,10) into a 6-plane case, a 4-line case and a light
case. The deletion route covers most of it instead. Delete a basis `S` with `M \ S` uniformly
dense. Then KUM(4,6) (by duality) orders `M \ S`, and an extension step reinserts `S`.

* `xcyc6_restricted.py`: X′(6) holds when `M` is strict with t = 0 (UNSAT in 1 s, with or without
  the light caps). The failures of plain X′(6) all come from non-strict or t>0 matroids.
* `hit10.py`: does a deletable basis exist at k = 2?

  | case | deletable basis |
  |---|---|
  | no 6-plane, no 4-line | always (Lemma H) |
  | 4-line, no 6-plane | always (UNSAT, < 1 s) |
  | 6-plane | not always (SAT) |

* Strict t=0 on 10 elements with no deletable basis forces every element to have a parallel
  partner (UNSAT in 8 s with one unpaired element). So `E` is five parallel pairs, and the
  simplification is `U_{4,5}`: four coplanar points would make an 8-element plane. Such a
  matroid has the explicit cyclic basis ordering `a₁ … a₅ a₁′ … a₅′`.

So strict t=0 KUM(4,10) reduces to three pieces:

* (a) the paired case, an explicit construction;
* (b) "an unpaired element gives a deletable basis", currently a small SAT claim;
* (c) the restricted X′(6), a small SAT claim in the X′ family.

## hit14g and hit14line

`hit14g` is the choice lemma of Theorem G at `k = 3`. Its paper proof, three cases on `r(C)`, is
in `RANK4_HEAVY_FLAT_SPLICE.md` §7. `hit14line` (a 6-line, no 9-plane) has no written proof yet.
Both are specific to `n = 4k+2`, so they matter only for rank 4.

## X′ and the linear lemma X

These are the core claims. They are pure basis-exchange statements with no density hypothesis. A
human proof would be the natural next research target. However, the first rank-5 probes
(`RANK5_EXTENSION_PROBE.md`) find X′₅ SAT at N = 10 and 15, so the rank-4 form of X′ may not
transfer to rank 5 unchanged.
