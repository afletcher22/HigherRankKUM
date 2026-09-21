# Rank-4 t=0 one-step saturation research

Date: 2026-09-21.

Branch: `rank4-t0-one-step-saturation-research`.

Status: mathematical / computational research checkpoint.  The conjectures in
this note are **not Lean-certified** unless explicitly stated otherwise.

## Why this branch exists

Astra's exact six-defect saturated selector is false.  The current upstream
gap is therefore not a selector theorem but the implication from persistent
four-block lifting failure to a saturated rank-three flat.

The experiments below suggest a sharper target than the component statement.

## One-step blocker-saturation conjecture

Let `M` be in the strict rank-four t=0 branch on `4k+2` elements, let
`e` be the fixed omitted element, and let `sigma` be a rank-four CBO of
`M \ e` on `4k+1` elements.

Assume `sigma` is bad for insertion of `e`.

If **no CBO-preserving permutation of four consecutive entries of sigma is
favorable for e**, then some blocker triple `T` of `sigma` satisfies

`|cl_M(T) ∩ (E(M)-e)| = 3k-1`.

Under the already-certified no-dangerous cap this says that
`cl_M(T)` is a rank-three flat of exactly `3k` elements containing `e`.

This is stronger than the four-block component dichotomy: a closed all-bad
four-block component automatically has no favorable one-step neighbor.

## Falsification evidence

A new deterministic stress audit tests the contrapositive:

> if no rank-three flat of size `3k` contains the omitted element, every bad
> deletion CBO has a favorable one-step four-block neighbor.

### Exact pointed n=10 audits over odd fields

For each selected represented matroid and each omitted element having no
6-point rank-three flat through it, **every deletion CBO was enumerated**.

GF(3), seed 314159:

- 8 robust simple matroids;
- 26 pointed no-saturation cases;
- 77,896 deletion CBOs;
- 19,854 bad CBOs;
- 0 one-step violations.

GF(5), seed 271828:

- 4 robust simple matroids;
- 22 pointed no-saturation cases;
- 115,398 deletion CBOs;
- 11,066 bad CBOs;
- 0 one-step violations.

The complete binary n=10 census is not discriminating for this particular
conjecture: every pointed orbit representative already lies on at least one
6-point rank-three flat.  It still contains 2,268 bad states at fixed-e
four-block distance at least two, so one-step repair is certainly false
without the no-saturation alternative.

### Higher-k ternary stress

Simple GF(3) samples were tested with the omitted element restricted to
elements lying on no saturated `3k`-point rank-three flat.

- n=14, k=3: 10 matroids x 30 bad states = 300; 0 violations.
- n=18, k=4: 8 matroids x 20 bad states = 160; 0 violations.
- n=22, k=5: 5 matroids x 15 bad states = 75; 0 violations.

Thus the same one-step dichotomy survived 535 sampled higher-k bad states.

This agrees with the existing nonrepresentable-style n=14 sparse-paving
stress: all 71 sampled bad states repair in one fixed-e four-block move, while
rank-three flats there are far below the 9-point saturation threshold.

### Historical n=14 binary witness

Replaying the existing 70 fixed-e sampled bad states:

- 7 sampled states are not one-step repairable;
- every one of those 7 has a 9-point rank-three flat through the omitted
  element;
- for the two omitted labels in that sample having no such saturated flat,
  all sampled bad states are one-step repairable.

Moreover, every one of the seven rigid states has at least one **blocker
triple whose own closure is saturated**, supporting the stronger blocker form
rather than merely existence of an unrelated saturated flat.

## A local blocker-push lemma

Write the local deletion order as

`..., x[-1], x0, x1, x2, x3, x4, x5, x6, ...`

and suppose:

1. `T0={x0,x1,x2}` is a blocker for `e`;
2. the triple at start `i-1` is a nonblocker;
3. the triples at starts `i+1` and `i+2` are nonblockers.

Consider the adjacent swap `x2 <-> x3` (the `swap23` four-block move).

### If the swap preserves the deletion CBO

The moved triple at start `i` is `{x0,x1,x3}`.

It cannot be a blocker.  Otherwise `e` is in the closures of both
`{x0,x1,x2}` and `{x0,x1,x3}`; their union is the old basis
`{x0,x1,x2,x3}`.  The certified closure-intersection mechanism then gives

`e in cl({x0,x1})`.

But `{x0,x1}` is contained in the old triple at start `i-1`, which would
make that triple a blocker, contradiction.

After the swap, the triples at starts `i+1` and `i+2` are unchanged as
sets.  Therefore the first three starts `i,i+1,i+2` are nonblockers.

Consequently, if the new CBO is still bad, its triple at start `i+3` must be
a blocker.  In other words, inside an all-bad component the valid adjacent
swap **pushes a blocker three starts forward**.

### If the swap does not preserve the deletion CBO

Only two rank-four windows change as sets:

- the left boundary replaces `x2` by `x3` in
  `{x[-1],x0,x1,x2}`;
- the right boundary replaces `x3` by `x2` in
  `{x3,x4,x5,x6}`.

Hence failure gives one of the explicit closure incidences

`x3 in cl({x[-1],x0,x1})`

or

`x2 in cl({x4,x5,x6})`.

This uses exactly the existing one-element failed-exchange lemma.

So this single probe has the van-den-Heuvel--Thomasse-style form:

`valid push -> blocker propagates`

or

`invalid push -> structural closure obstruction`.

No representability, simplicity, strict density, or no-dangerousness is
needed for the local lemma itself.

## Why this looks useful

The 2009 weighted cyclic-ordering proof chooses a closure-maximal placement
and repeatedly pushes elements.  A push either strictly improves the closure
profile or, in a periodic best configuration, forces a tight structural set.

The local lemma above gives an analogous mechanism for the t=0 lifting
problem.  In a closed all-bad four-block component, a valid probe cannot
escape to success, so it transports a blocker.  An invalid probe emits a
rank-three closure incidence.  The proposed global proof should propagate
these incidences until one blocker flat reaches the certified maximum
`3k-1` deletion elements.

This avoids the scalar potentials already falsified in
`RANK4_FOUR_BLOCK_STATE_RESEARCH.md`.

## Next mathematical task

Develop the symmetric and short-zero-run push rules for the remaining local
blocker-run patterns, using the existing seven move types:

- adjacent swaps for one-element pushes;
- endpoint/side swaps for skip-one transposition probes;
- pairShift/canonicalTwist for the genuine 2+2 boundary cases.

The target is a finite local transition table with the following output at
each bad state:

1. a CBO-preserving push to another state in the same all-bad component; or
2. an ambient closure incidence attached to a specific blocker flat.

Then prove that a periodic push sequence with no favorable state forces one
blocker closure to have complement at most `k+2`.  The certified
no-dangerous cap gives the reverse inequality, hence complement exactly
`k+2` and blocker-flat size exactly `3k-1`.
