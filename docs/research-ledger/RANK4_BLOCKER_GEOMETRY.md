# Rank-4 blocker geometry

Date: 2026-09-20/21.

Branch: `rank4-blocker-geometry`.

Certified checkpoint:

`0d0aa8fbe121696f5ba5ebd16c2c3f46259439db`

Full root CI: green.

## Purpose

This package formalizes the representation-free local geometry behind the
post-t>0 deletion/insertion program.  It does not prove favorable insertion;
it supplies the exact blocker facts that later global selection arguments may
use.

## Certified closure core

`HigherRankKUM/BlockerClosure.lean` proves:

* `mem_closure_inter_of_indep_union`: if `X union Y` is independent and
  `e` lies in both closures, then `e` lies in the closure of `X intersect Y`;
* triple and fourfold versions for successive overlaps;
* `mem_closure_iff_contractElem_dep`: for a nonloop `e` and an independent
  set `T` avoiding `e`, the blocker condition `e in cl(T)` is equivalent
  to dependence of `T` in `M / e`;
* `fundCircuit_subset_insert_of_subset_of_mem_closure`;
* `fundCircuit_eq_of_common_spanning_subset`: a blocker set common to two
  basis windows forces the fundamental circuit of `e` to persist across the
  slide;
* `not_four_closures_of_nonloop_of_fourfold_inter_empty`.

## Certified cyclic adapter

`HigherRankKUM/Rank4/BlockerCycle.lean` adds:

* `blockerAt`;
* `cyclicWindow_three_union_next_eq_four`;
* `cyclicWindow_three_disjoint_shift_three`;
* `four_successive_triples_inter_empty`;
* `no_four_consecutive_blockers`.

The final theorem says that on any rank-four cyclic basis ordering of length
at least six, the blocker word for a nonloop cannot contain four consecutive
ones.

This is exactly the closure-intersection statement from the Astra
deletion/insertion report, now connected to the repository's actual
`CyclicBasisOrder` interface and root-import certified.

## Interpretation

For a deletion CBO `sigma=(x_i)`, blockers are ordinary dependent triples in
the rank-three contraction `M/e`.  Consecutive blockers therefore represent
low-rank concentration, not merely a binary-word artifact.

The theorem is deliberately only local.  A bad deletion CBO can still have
both blocker runs and nonblocker runs of length at most three, so
`no_four_consecutive_blockers` does not imply insertability.

The next global target should connect persistent bad blocker patterns to
saturation of a rank-three flat.  Exact binary n=10 computation on the
separate favorable-state branch strongly suggests that genuine eligible
fixed-element insertion failure forces a dangerous hyperplane.
