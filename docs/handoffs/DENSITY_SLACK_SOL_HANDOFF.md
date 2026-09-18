# Sol handoff: repair build fixes and good-deletion theorem

## Preservation and branch

Started from `rank4-sprint5-six-block-audit` at
`6d7a425d9fc5adf7089589db3d6271a4b3d5d4fd`.
All changes are isolated on `rank4-density-slack-continuation`.
The original research branch, main, frozen vendor, and dependency pins were
not modified. The continuation workflow adds three previously omitted endpoint
modules to its targeted build. Validation PR #15 is used only to pin CI runs;
it was closed during Python/docs commits to avoid duplicate builds.
Nothing was merged.

## Lean corrections

- `8ea5d8811a7661052fd67bd752400d204db858e5`: explicitly change the permutation
  goal to the orbit equivalence composition before using `ofFn_comp_perm`.
- `3399542f5242ccb15c0556aa339fe2c882c8e9ef`: add `3 < N` to
  `crossRepairCanonicalElement_offset_other`. This is a real missing premise,
  not merely a tactic workaround: raw offsets 2 and 3 may wrap for small N.
- `abc9664e11ea2a58f0f28b3749c872a268a37a4d`: update all four callers in the
  parity bridge, where the existing `5 < N` already supplies the premise.

Pinned CI run: https://github.com/afletcher22/HigherRankKUM/actions/runs/35384252627
The targeted Lean step and ALL existing computational certificate steps passed.
The full build reached new modules and failed on pair-set simplification in
GcdTwoRankTwoTight and a missing `open PairCycle` for `bitPick` in
GcdTwoCrossRepairParity. GcdTwoClosurePropagation compiled successfully.

Follow-up fixes: b6d0ff8c (explicit encard_pair and pair membership), 27c21c89
(open PairCycle), f0c29d8b (target all three newer endpoint modules).
Second pinned source/workflow checkpoint:
`f0c29d8b324cb3b69e2aeb9f9960e4926d9af20d`.
Second run: https://github.com/afletcher22/HigherRankKUM/actions/runs/35385259860
Do not infer a full green build from a targeted step alone.

## New mathematics (checked informal, NOT Lean formalized)

Read `docs/research-ledger/DENSITY_SLACK_DELETION.md` for full proofs.

1. For uniformly dense finite M with n>r>0, every deletion is uniformly dense
   iff the integer profile satisfies `n*j-r*m_j >= j` for 1<=j<r.
2. Every deletion of a strictly uniformly dense integral-density matroid
   (`n=k*r`, k>=2) is uniformly dense, in arbitrary rank.
3. In strict rank four at n=4k+2, k>=1, a deletion fails exactly when its
   element lies outside a rank-three flat of size 3k+1.
4. The complements of these dangerous hyperplanes are pairwise disjoint,
   each has size k+1, and there are at most three. The EXACT number of good
   deletions is `4k+2-t*(k+1)`, hence at least k-1.
5. Thus every strict even-size rank-four instance of size at least eight
   admits a uniformly dense deletion. Its odd-size CBO follows mathematically
   from the external coprime theorem. Reinsertion remains unproved.

The k-1 bound is sharp for EVERY k>=1: over GF(2), take k copies of each
of a,b,d, k-1 copies of c, and single a+c,b+c,d+c, with a,b,c,d independent.
The research note proves strict density and identifies precisely the c copies
as good deletions. The k=1 boundary example consequently cannot be removed.

No novelty claim is made. Do not silently import the external coprime theorem
as a custom Lean axiom. Do not present these proofs as Lean-certified.

## Regression and insertion obstruction

`python3 experiments/density_slack_deletion_certificate.py` checks all subsets
of two historical witnesses, a six-element boundary example, and 160 seeded
binary examples. Compare JSON with `density_slack_deletion_result.json`.
110 of the sampled examples are uniformly dense; 70 are strict, including
25 integral and 45 gcd-two examples. This sample is not a classification.

The eighteen-element witness attains the good-deletion lower bound: exactly
three good labels (2,9,15). The six-element example has no good deletion,
showing why the existence statement excludes k=1.

The ten-element witness has four good labels: 0,4,7,8. Exhaustion of all
deletion CBOs modulo rotation and all single insertion gaps gives:

| Label | Deletion CBOs | CBOs permitting insertion |
|---|---:|---:|
| 0 | 368 | 56 |
| 4 | 368 | 56 |
| 7 | 224 | 88 |
| 8 | 336 | 56 |

EVERY good label has orders that do not extend by a single insertion gap.
Therefore even "some good label works with every deletion CBO" is false.
The viable sufficient target must choose both the element and order, or permit
reordering/multiple-gap operations. This is not a KUM counterexample.

## Recommended continuation

First finish any remaining full-build repairs using the exact CI diagnostics.
Then audit/formalize the good-deletion argument as a bounded result, especially
the disjoint dangerous-complement lemma. It unifies deletion availability for
both remaining even rank-four size classes, but does not replace the current
closure/slack repair route. Investigate a controlled order-selection or
reinsertion theorem; avoid the now-refuted every-order quantifiers.

For closure propagation, integer slack gives a fixed capacity bound on any
single flat. The profile does not change under repair and is not an ascent
potential. A proof still must show that incidences accumulate in the SAME flat.
