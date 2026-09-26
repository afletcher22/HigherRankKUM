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

Refinements:

* **X′(6) needs only "every plane has at most 6 elements".** It is UNSAT with just that
  constraint, even with loops allowed, and SAT once 7-element planes are allowed. It needs no
  density of `M` or of `M \ S`. Statement: *in a rank-4 matroid on 10 elements whose planes have at
  most 6 elements, a cyclic basis ordering of `M \ S` (S a basis) extends to one of `M`.*
  Certificate: `xcyc6p`, 96k hints.
* (b) as one claim (`hit10u`) needs 3.27M hints, which is too big. Split by case, it is small:
  * no 6-plane and no 4-line: Lemma H (Lean, human);
  * 4-line and no 6-plane: `hit10line`, **2.6k hints**, a candidate for a hand proof;
  * 6-plane with an unpaired element inside the plane: `hit10planeU0`, 120k hints;
  * 6-plane with an unpaired element outside the plane: `hit10planeU9`, 121k hints.
* Total for the new route is about 340k hints, against about 2.3M for the five current
  certificates. The proof then has the same shape at `k = 2` as at `k ≥ 3`: a hitting lemma, the
  induction (KUM(4,6) by duality) and X′, plus one explicit exceptional matroid.

## KUM(4,10) from a pair chain (adopted)

A literature review (2026-09-26) turned up two sources of *pair chains*: cyclic sequences of
disjoint pairs `P_0 .. P_{m-1}` with every `P_i ∪ P_{i+1}` a basis.

* **van den Heuvel–Thomassé.** Theorem 2.1 with weight 2 on `ZMod (2k+1)` makes every arc
  `φ⁻¹(x) ∪ φ⁻¹(x-1)` a basis. For a rank-4 matroid on `4k+2` elements the fibre sizes satisfy
  `f(x) + f(x-1) = 4` around an odd cycle, so every fibre has 2 elements. Every uniformly dense
  rank-4 matroid on `4k+2` elements therefore has a chain of `2k+1` pairs. This settles the
  existence question left open for the pair-cycle layer of the main library (`PairCycle*.lean`,
  `docs/RANK4_COVERAGE.md`).
* **Wiedemann** (*Cyclic base orders of matroids*, 1984 note, typed 2006). For bases
  `B_1 .. B_l` and a split `B_1 = X_1 ⊔ Y_1` there are splits `B_i = X_i ⊔ Y_i` with every
  `Y_i ∪ X_{i+1}` a basis. With `|X_1| = 2` this gives a chain of `2k` pairs for `n = 4k`.

**Orienting a chain.** The windows that start inside a pair are `{last(P_i)} ∪ P_{i+1} ∪
{first(P_{i+2})}`. The relation `R_i` (pairs `(u, v)` making this a basis) has no empty row or
column. A cycle of `i → i+2` fails to orient only if every `R_i` on it is a permutation and their
Z/2 parities sum to the wrong value: the chain is *rigid*. A rigid 5-pair chain, relabelled along
its dependent matchings as `Z_10`, is exactly:
* bases `m + {0,3,5,8}` and `j + {0,3,6,8}`;
* rank 3 for `j + {0,1,3,8}`.
Nothing else is forced (`rigid10.py`).

**Re-splits.** A re-split cuts one window `P_x ∪ P_{x+1}` into two other pairs. Results from
`pairchain.py` (no hypotheses beyond the chain unless stated):

| n | chain | question | result | hints |
|---|---|---|---|---|
| 10 | vHT, 5 pairs | a CBO within one re-split | UNSAT | 17k (14.7k ungated) |
| 8 | Wiedemann, 4 pairs | a CBO within one re-split | UNSAT | 6k |
| 12 | Wiedemann, 6 pairs | within one re-split | SAT | |
| 12 | Wiedemann, 6 pairs | within two re-splits | UNSAT | 2.4M |
| 14 | vHT, 7 pairs | within one re-split (even strict t=0) | SAT | |
| 14 | vHT, 7 pairs | within two re-splits | UNSAT | 749k |

A single rigid chain can also have no pair deletion (`P_{i-1} ∪ P_{i+2}` never a basis). A
12-element one-window local version of the re-split lemma is false (`localsplit.py`).

**Adopted for n = 10.** Claim `chain10` in `lean_witness_f.py` lists the orientations of the chain
and of every one-window re-split, with no gating and no density bounds: 14,738 hints, 2,737 core
clauses. It replaces the tight/dangerous case split and all five certificates (about 2.3M hints)
on branch `probe/rank4` (`Probe/Chain10.lean`, `Probe/Rank4/Kum10Chain.lean`).

**For n = 14** the two-re-split claim (749k) would replace hit14g + hit14line + X′(10) (about
924k): a modest saving. X′(10) is used only at n = 14.

## Paving and the extension theorem

McGuinness (*Cyclic orderings of paving matroids*, EJC 31(4) 2024, Proposition 13) proves X′ for
paving matroids in every rank, with no density hypothesis. `ext_rank_r.py` options `paving` and
`indepJ` (every set of at most J elements independent) give:

| claim | general | simple (indep2) | paving |
|---|---|---|---|
| X′₄(6) | SAT | UNSAT | UNSAT |
| X′₅(10), w = 7 | SAT | SAT | UNSAT (49 s) |
| X′₅(15), w = 7 | SAT | | UNSAT (206 s) |

So every failure of the naive extension involves circuits of size at most 4 through `S`.

## KUM(5,10) is known

Garamvölgyi, Mizutani, Oki, Schwarcz and Yamaguchi (ICALP 2025, arXiv 2411.06771, Proposition
4.3) show by SAT that in rank at most 5 the only basis pair without an SI-ordering is `R10`, and
`R10` satisfies Gabow's conjecture (Bérczi–Mátravölgyi–Schwarcz). Hence Gabow's conjecture, and
KUM(5,10), hold up to rank 5. Our run of `kum_r_n.py 5 10` is an independent confirmation. Kotlar
(2013) gives only exchanges of length at most 6 in rank 5, despite being cited for rank 5.

## hit14g and hit14line

`hit14g` is the choice lemma of Theorem G at `k = 3`. Its paper proof, three cases on `r(C)`, is
in `RANK4_HEAVY_FLAT_SPLICE.md` §7. `hit14line` (a 6-line, no 9-plane) has no written proof yet.
Both are specific to `n = 4k+2`, so they matter only for rank 4.

## X′ and the linear lemma X

These are the core claims. They are pure basis-exchange statements with no density hypothesis. A
human proof would be the natural next research target. However, the first rank-5 probes
(`RANK5_EXTENSION_PROBE.md`) find X′₅ SAT at N = 10 and 15, so the rank-4 form of X′ may not
transfer to rank 5 unchanged.
