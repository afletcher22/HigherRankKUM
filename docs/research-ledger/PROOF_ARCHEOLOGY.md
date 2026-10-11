# Proof archeology of the rank-4 proof (2026-10-10)

**Goal.** Before a Palomar submission, look for parts of the rank-4 proof that can be removed,
generalized or simplified without golfing. Everything below is measured on the import closure of
`Probe.Rank4.Final` (the theorem `solvesKUMAtRank_four`), counting Lean source lines.

| state | modules | lines | rank-3 theorem (vendored Rank3KUM) |
|---|---|---|---|
| `probe/rank4` at `af49194` (human `k = 3` hitting cases) | 134 | 31,793 | used (54 modules, 12,306 lines) |
| `probe/rank4` at `9860df7` (this note) | 64 | 13,277 | not used |

The new head builds and replays with `[propext, Classical.choice, Quot.sound]` (CI run
38105176177; the whole job takes under 5 minutes, peak memory 3.4 GB).

## 1. Where the size was

The `4k+2` step (`k ≥ 3`) has three branches in `Full.lean`:

* a nonempty proper tight set: the rational tight reduction (about 1k lines), whose only external
  input is rank-2 KUM at the odd size `2k+1`, which is coprime KUM;
* strict with a dangerous plane (`3k+1` elements): the dangerous-hyperplane schedule of the main
  library (about 5k lines), which needs rank-3 KUM at every size, so the whole vendored Rank3KUM
  (12k lines);
* strict, `t = 0`: the hitting lemma, then induction and pair-chain insertion (XP).

The tight branch pulled in Rank3KUM only by accident: `solvesKUMAtRankSize_two_odd` sits in
`PrimeRank.lean` next to `solvesKUMAtRank_three`. Semantically, Rank3KUM and the schedule
machinery served only the dangerous branch.

## 2. The dangerous branch by deletion (done)

**Question.** Does the deletion step (a basis `S` with `M \ S` uniformly dense) work without
strictness or `t = 0`? The ledger had only asked it for strict `t = 0` matroids, since the other
branches were already handled.

**Evidence.**

* SAT at `n = 14`, uniform density only, split by the non-strict flat present
  (`hit_sat14_nonstrict.py`, run on GitHub Actions by `.github/workflows/experiments.yml`):
  a 10-plane: UNSAT (122 s); a 7-line and no 10-plane: UNSAT (8 s). With the strict case (Lemma H
  and `HitThree`), every uniformly dense rank-4 matroid on 14 elements has a deletable basis.
* Random search (`hit_nonstrict.py`): 380 uniformly dense instances at `k = 3, 4` over GF(3),
  GF(5), GF(7), most with a dangerous plane or a tight line, all with a deletable basis.
* The construction below (`dangerous_choice.py`): 360 strict instances with a dangerous plane at
  `k = 3, 4, 5`, 81 of them with two dangerous planes; for every tested Edmonds partition, some
  triple works.

**Lemma D** (`Hitting.hitDanger`, `probes/Probe/Rank4/HitDanger.lean`, 818 lines, human). A
strict rank-4 matroid on `4k+2` elements, `k ≥ 3`, with a plane `P` of `3k+1` elements has a
deletable basis.

*Proof.* Profile: points `≤ k`, lines `≤ 2k`, planes `≤ 3k+1`; `C = E - P` has `k+1` elements.

1. Some `e₀ ∈ P` lies on no `k`-point: four disjoint `k`-points would need `4k > 3k+1` elements.
2. `M | (P - e₀)` has rank 3, `3k` elements and at most `k r(X)` elements in every `X`, so by
   Edmonds it splits into `k` independent triples `D_x`. Counting the traces (they add up to the
   size of any subset of `P - e₀`): every triple meets every `k`-point and every `2k`-line of `P`.
   So rank-1 and rank-2 subsets of `P - D_x` have at most `k-1` and `2k-1` elements.
3. Choose `c ∈ C`: in the `k`-point of `C` if there is one; else outside a basis of `M | C`; else
   (`C` independent) anywhere. In the first two cases `C ⊆ cl(C - c)`, so two distinct planes
   through `C₀ = C - c` meet inside `cl(C)`, which has at most `k-1` elements in `P`. In the third,
   `C₀` has rank `k ≥ 3`, so only one plane contains it. Every point of `C₀` has at most `k-1`
   elements.
4. A plane `F ≠ P` through `C₀` is *bad* for `x` if `|F ∩ P - D_x| ≥ 2k-1`. A plane is bad for at
   most one triple (counting over the triples on the line `F ∩ P`). Three planes that can be bad
   would need `(2k-1) + k + k > 3k+1` elements of `P`. With `k ≥ 3` triples, some `D_x` is bad for
   no plane.
5. `D_x + c` is deletable. For `X` outside it of rank `j`, `X ∩ P ⊆ P - D_x` and `X - P ⊆ C₀`
   (`k` elements). Steps 2 and 3 give the bound at ranks 1 and 2. At rank 3 it can fail only if
   `X ⊇ C₀`; then `cl(X)` is a plane through `C₀` and step 4 applies. ∎

**Wiring.** `Full.lean` sends the dangerous case through the same deletion, induction and XP tail
as the `t = 0` case, and calls the rational tight reduction with coprime KUM directly
(`VHT.solvesKUMAtRankSize_of_coprime`), so it no longer imports `Rank4/Unconditional.lean`.
`Hitting.lean` defines `DangerousPlane` and `isFlat_inter` itself instead of importing
`Rank4/GcdTwoDeletion.lean` (691 lines). Effect: 134 → 66 modules, 31,793 → 14,164 lines.

## 3. The SAT layer (done)

The only certificate left is `chain10`, but the closure still carried the hitting and extension
encodings. `MaskBridge.lean` now holds the five helpers the `chain10` bridge used from
`ExtBridge.lean`; `Cert.lean` drops the `h_certificate` command; `ExtBridge`, `ExtEnc` and `EncH`
are removed. Effect: 66 → 64 modules, 14,164 → 13,277 lines.

## 4. Options measured but not taken

| option | saves | status |
|---|---|---|
| tight branch by deletion too | 7 modules, 968 lines | true at `n = 14` (SAT above); no proof for general `k` yet. It would make the `4k+2` step uniform: every uniformly dense rank-4 matroid on `4k+2 ≥ 14` elements has a deletable basis. |
| `n = 6` without the general rank-2 solver | 6 modules, 1,103 lines | needs a direct proof. In the rank-2 dual, a CBO is a cyclic order with no two cyclically adjacent elements parallel, which exists when every parallel class has at most `n/2 = 3` elements. |
| `n = 8` by XP instead of Kotlar–Ziv | 1 module, 129 lines | XP(4) holds even with one fixed pairing (`xpair.py 4 noshift`: UNSAT), but XP itself uses Kotlar–Ziv's helper lemmas, so `SerialExchange.lean` stays. Not worth it. |

## 5. Generalizations for later work

* **Theorem D is rank-generic in substance.** Only the literal 4 and `Rank4Extension` make it
  rank-4. For a prime rank `p`, `PrimeRank.lean` already turns divisible KUM into full KUM, so
  KUM at rank `p` reduces to KUM(`p`, `2p`) and an extension theorem on `pk` elements (`k ≥ 2`).
  Theorem D only applies the extension when `M - S` is a disjoint union of bases. That hypothesis
  is much weaker than X′'s (no density), and it is the relevant target for rank 5: the rank-5
  probes found X′₅ SAT only with local block encodings, and KUM(5,10) is known.
* **The deletion step is the uniform way to handle `gcd(n, r) > 1`, `n` not divisible by `r`.**
  With Lemma D, everything in rank 4 except one small branch (the tight set, `n = 4k+2`) goes
  through "delete a basis, induct, extend". The rank-4-specific inputs are XP and the hitting
  lemmas.

## 6. Palomar dry run (2026-10-10)

Branch `palomar/dry-run` added `Challenge.lean` (Mathlib-only statement `rankFourKUM`),
`Solution.lean`, `comparator.json`, a draft `formalization.yaml`, a root MIT `LICENSE`, and a
workflow that calls Palomar's own verifier (`PalomarSubmission` `submission.yml` at
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, profile `palomar-standard-v1`, mode `full`).

* `Challenge` and `Solution` build; `HigherRankKUM.Palomar.rankFourKUM` depends on the standard
  axioms only. The license (MIT) and metadata passed preparation.
* Preparation failed on `source.module_required`: since PalomarSubmission #155 (2026-09-28), every
  `.lean` file in the submitted tree must start with the `module` header and use the module
  system, and each file has at most 10,000 lines. All 209 Lean files in the repository were
  flagged, including the vendored Rank3KUM and modules outside the proof.
* So the submission tree should contain only the proof's closure (now 64 modules, no vendored
  code, plus `Challenge` and `Solution`), ported to the module system. The certificate commands in
  `Cert.lean` run Lean code at elaboration time (`unsafe evalTerm` on `include_str` strings) and
  will need `meta` handling in the port.
