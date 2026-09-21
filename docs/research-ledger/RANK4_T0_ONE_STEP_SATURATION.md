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

Moreover, every one of the seven rigid states has at least one blocker triple
whose own closure is saturated.  This remains useful evidence for a common
direct mechanism, but the complete binary n=10 census shows that it is not
universal.


## Universal three-probe reduction

The blocker-word part of the one-step problem collapses much further.

Let `b_i` be the cyclic blocker word of a bad deletion CBO.  The cycle has
odd length `4k+1`, contains both 0 and 1, has no `0000` because the state
is bad, and has no `1111` by the certified blocker theorem.

A simple run-length argument shows that at least one of the following local
patterns occurs:

1. `0010`;
2. `0110`;
3. `01?10`, where `?` is arbitrary.

Indeed, if some 1-run has length two we get (2); if some 1-run has length
three we get (3) with `?=1`; otherwise all 1-runs are singletons.  Then,
unless a zero-run has length at least two, the word alternates 0 and 1 around
an odd cycle, impossible.  A zero-run of length at least two followed by a
singleton 1 gives (1).

Each pattern has a concrete four-block permutation which, **if it preserves
the deletion CBO**, is forced to create four consecutive nonblockers.

### Probe A: pattern 0010

Suppose the old triple starts `s+1,s+2,s+3,s+4` have statuses
`0,0,1,0`.

Apply local permutation

`(0,1,3,2)`,

i.e. swap local positions 2 and 3.

The new triple starts `s+1` and `s+2` are the same old triples.  The new
triple at `s+3` shares the pair `{x4,x5}` with the old blocker at
`s+3`; if it were also a blocker, closure-intersection inside the old basis
would force `e in cl({x4,x5})`, contradicting that the old triple at
`s+4` is a nonblocker.  The start `s+4` is unchanged.  Thus a valid probe
creates `0000`.

Only two rank-four windows change as sets, at starts `s-1` and `s+3`,
and each is a single-element exchange.

### Probe B: pattern 0110

Suppose starts `s-1,s,s+1,s+2` have statuses `0,1,1,0`.

Apply

`(1,0,3,2)`,

simultaneously swapping the first pair and the last pair of the four-position
block.

The target starts `s-1,s,s+1,s+2` become nonblockers: the extreme two are
unchanged as sets, while the middle two are ruled out by
closure-intersection against the neighboring old nonblockers.

Exactly four rank-four boundary windows change as sets, at starts
`s-3,s-1,s+1,s+3`.  Each differs from an old basis by one element.

### Probe C: pattern 01?10

Suppose starts `s,s+1,s+3,s+4` have statuses `0,1,1,0`; the status at
`s+2` is irrelevant.

Apply the local right rotation

`(3,0,1,2)`.

The target starts `s+1,s+2,s+3,s+4` are forced nonblockers.  The two
interior new triples are excluded by closure-intersection with the old
blockers at `s+1` and `s+3`, using the old nonblockers at `s` and
`s+4`.

All six noncentral boundary windows change, but again **every one is only a
single-element exchange** from an old basis.

### Consequence for a one-step-rigid state

For every one-step-rigid bad state, one of Probes A--C applies and must fail
to preserve the deletion CBO.  Since every changed boundary window for these
three probes is a one-element exchange, the existing theorem

`LocalExchangeClosure.mem_closure_of_failed_base_exchange`

turns the failure into an explicit rank-three closure incidence.

This is a substantial simplification over the earlier seven-move / 2+2
program: the proof of the one-step saturation dichotomy can, in principle,
be carried out using only **three probes and single-exchange closure
geometry**.  The common-base rank-two machinery is not needed for this
reduction.

The symbolic reduction was exhaustively checked on every abstract bad blocker
word up to cyclic reversal for lengths 9, 13, and 17.  The run-length proof
above removes the size restriction.


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
rank-three closure incidence.  The proposed global proof should propagate these incidences until either
(a) one blocker flat reaches the certified maximum, or (b) the blocker pattern
falls into a periodic indirect-saturation configuration such as
`001001001`, from which a saturated flat through `e` is forced by a
different combination of local incidences.

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
of two endpoints:

1. a blocker closure is saturated; or
2. a periodic indirect-saturation pattern forces some other rank-three flat
   through `e` to have size `3k`.

The second endpoint is essential: the binary period-three witness shows the
first endpoint alone is false.
