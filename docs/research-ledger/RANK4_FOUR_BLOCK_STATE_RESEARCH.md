# Rank-4 four-block state research

Date: 2026-09-20/21.

Branch: `rank4-four-block-state-research`.

Status: computational research checkpoint.  None of the move-graph claims in
this note are Lean-certified unless explicitly identified as imported from a
separate green branch.

## State graph

A state is `(e,sigma)`, where `sigma` is a cyclic basis ordering of
`M \ e`.

The enlarged local move set studied here is:

1. **four-block reorder**: choose four cyclically consecutive positions of
   `sigma`, apply any permutation to those four entries, and keep the move
   only if the resulting order is again a deletion CBO;
2. **point pivot**: exchange the omitted element `e` with one entry of
   `sigma`, again keeping the move only if the new deletion order is a CBO.

Adjacent swaps are already special cases of four-block reorders, so they do
not need to be listed separately in the final formulation.

A state is successful exactly when its blocker word has a zero-run of length
at least four.

## Why enlarge the old graph?

Astra's original graph using adjacent swaps plus point pivots can have closed
all-bad components.  Even adding arbitrary single transpositions does not
remove every such component in the exact binary non-simple n=10 class.

The four-block move is the first tested enlargement that consistently removes
those obstructions.  It is also rank-four natural: it acts at the scale of one
basis window / one local 2+2 repair.

## Exact binary n=10

For the complete binary represented n=10 class satisfying the exact
two-deletion flat caps (2,4,6):

- 28,476 multiplicity patterns;
- 16 GL(4,2) orbits;
- zero prescribed-element lifting failures.

Using only the two canonical four-block patterns

- `[a,b,c,d] -> [c,d,a,b]`;
- `[a,b,c,d] -> [c,d,b,a]`;

together with adjacent swaps and point pivots, every one of the 16 exact joint
state graphs is connected.

The exact maximum distance from a state to success under this canonical move
set is **3**.

Allowing every four-position permutation does not reduce the worst exact
distance below 3: one orbit still has 32 states at distance 3.  Those hardest
states omit one of a parallel pair.

Thus:

> one-step repair is false, but radius three survives the complete binary
> n=10 two-deletion-robust represented class.

## Run-profile monotonicity is still not the proof

The lexicographic nonblocker-run profile is not a universal monotone potential.

With the two canonical four-block repairs, several exact n=10 orbits contain
states that cannot reach success along a nondecreasing profile path.

Even after every four-block permutation is allowed, one orbit still has 28
such states:

- 24 with profile `(3,3)`;
- 4 with profile `(2,2,2)`.

So the enlarged move graph does **not** resurrect the discarded monotone
run-profile theorem.  Successful repair can require a temporary decrease.

This is important: the evidence supports a short repair-path / closed-component
statement, not a descent theorem.

## Extremal sparse paving SQS(10)

For the 30-circuit-hyperplane Steiner quadruple system SQS(10), every fixed-e
deletion graph was enumerated exactly.

For every omitted element:

- 9,024 deletion CBOs;
- 8,496 successful states;
- one component under adjacent swaps plus the two canonical four-block moves;
- no closed all-bad component.

Thus all ten fixed-e graphs are exactly connected under the smaller canonical
move set.

Certificate:

`experiments/rank4_four_block_crossclass_stress.py`

## Odd-field n=10 stress

Deterministic GF(3) and GF(5) examples were tested, both simple and with
genuine parallel pairs, under the exact two-deletion flat caps (2,4,6).

No closed all-bad fixed-e component was found.

Fixed-e connectivity itself is too strong: one GF(3) parallel-pair example has
10 components, but every one of those components contains a successful state.
When point pivots are restored, that example's full joint graph is connected
in the separate audit.

This supports the weaker target:

> every relevant component contains success,

not universal fixed-e connectivity.

## Strict 4k: n=12 stress

Twenty binary non-simple n=12 matroids satisfying the one-deletion caps
(2,5,8) were sampled.  Ten deterministic bad states were selected from each,
for 200 states total.

Two canonical four-block moves:

- distance 1: 161;
- distance 2: 34;
- distance 3: 3;
- distance 4: 2.

All four-block permutations:

- distance 1: 188;
- distance 2: 12.

So the canonical pair-swap patterns are not enough for a universal
radius-three statement in the strict-4k branch, while arbitrary four-block
reordering is substantially stronger.

Certificate:

`experiments/rank4_n12_four_block_stress.py`

## t=0: n=14 stress

Ten binary n=14 t=0 matroids satisfying caps (3,6,9) were sampled:

- five ordinary random qualifying multisets;
- five deliberately forced to contain a 3-element parallel class.

Among 100 bad states, arbitrary four-block reorders plus pivots gave:

- distance 1: 92;
- distance 2: 7;
- distance 3: 1;
- no failure within depth 3.

The sample includes cap-saturating profile `(3,6,9)`.

Certificate:

`experiments/rank4_n14_four_block_stress.py`

## t=0: n=18 stress

The historical n=18 two-step-obstruction witness remains the hardest observed
example.

In the existing seeded type-state audit:

- two canonical four-block moves leave three closed all-bad 8-state
  components;
- allowing every four-block permutation eliminates all sampled failures
  within depth 4;
- observed all-four repair depths are 1, 2, or 3, with maximum 3.

A new unrelated random stress used ten further binary n=18 t=0 matroids:

- five random qualifying multisets;
- five with a deliberately forced 4-element parallel class;
- profiles include the exact cap `(4,8,12)`.

Across 41 sampled bad states:

- distance 1: 36;
- distance 2: 5;
- no depth-3 failure.

Certificate:

`experiments/rank4_n18_random_four_block_stress.py`

## Current conjecture

The strongest useful move-based candidate now worth trying to falsify is:

### Four-Block Favorable-Component Conjecture

Let `M` be a relevant strict rank-four instance and let `(e,sigma)` be a
state supplied by an eligible deletion.

In the graph generated by

- CBO-preserving permutations of four consecutive entries; and
- CBO-preserving point pivots,

the connected component of `(e,sigma)` contains a successful state.

For the t=0 branch, the hypothesis should include the certified
two-deletion-robust/no-dangerous conditions.  For strict 4k, only the
one-deletion package is presently certified, so the exact hypothesis may need
to differ.

A stronger empirical statement is:

> every tested bad state is within distance at most 3 of success.

This **radius-3 statement is only a falsification target**, not yet a theorem
candidate to formalize.  There is no structural proof of the numerical bound.

## Certified geometry already available

Separate green branches now provide the local ingredients:

- blocker = contraction dependence;
- closure intersection collapse;
- blocker fundamental-circuit persistence;
- no four consecutive blockers;
- cyclic rank-three capacity `|H| <= 3k` inside a `4k+1` rank-four CBO;
- saturated rank-three blocker set of size `3k` spanning `e` forces a
  dangerous hyperplane;
- therefore in the no-dangerous branch, a rank-three set in the deletion CBO
  spanning `e` has size at most **`3k-1`**.

The last endpoint is green on `rank4-t0-saturated-cap` at
`1354f0bf4c25f35fffdd95607c3f50421321ed05`.

## Suggested proof shape

Do **not** return to a scalar monotone potential.

The most plausible route is now:

1. choose an all-bad component of the enlarged four-block state graph;
2. use closure under every local four-position reordering and pivot to derive
   local common-base rigidity;
3. translate rigidity to closure incidences using the existing rank-two
   boundary-minor lemmas;
4. propagate those incidences across the component / cycle;
5. build a rank-three set of size `3k` spanning the omitted element;
6. contradict the certified no-dangerous cap `3k-1`.

This is closely analogous in spirit to the van den Heuvel-Thomasse proof:
their weighted theorem chooses a closure-maximal interval placement and shows
that failure of local pushes creates a structural tight obstruction.  Here the
local moves are four-block CBO reorders and pivots, and the forbidden terminal
obstruction should be a saturated rank-three flat.

## Next formal lemma

Formalize the **four-block move support** only:

- define permutation of four consecutive positions of a cyclic order;
- prove windows disjoint from the affected neighborhood are unchanged;
- isolate the bounded set of rank-four windows that must be rechecked;
- package a predicate saying the four-block reorder preserves the deletion CBO.

Do not formalize radius three, component success, or a monotone potential yet.
