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

## Saturation versus repair depth

A new audit tracks, for each bad state, how many blocker triples have
rank-three closure attaining the **maximum size allowed by the certified
no-dangerous cap** after the omitted element is removed:

`|cl(X) ∩ (E-e)| = 3k-1`.

Certificate:

`experiments/rank4_four_block_saturation_depth.py`.

### Exact hard binary n=10 orbit

For the 4,128-state orbit that contained the strongest earlier local-move
obstruction, the exact all-four-block-plus-pivot distances are:

- success: 1,856 states;
- distance 1: 2,112;
- distance 2: 128;
- distance 3: 32.

Among bad states, the number of saturated blocker closures shifts strongly
with distance:

| distance | saturated-blocker count -> states |
|---:|---|
| 1 | 1->128, 2->1024, 3->640, 4->192, 5->128 |
| 2 | 4->96, 5->32 |
| 3 | 5->32 |

Every distance-three state has exactly five blockers and **all five blocker
closures are saturated at `3k-1=5`**.  All 32 omit one of the two parallel
copies of the same projective point.  Moreover, each such state has only one
nonidentity CBO-preserving four-block permutation anywhere around the cycle.

A shortest distance-three repair path first breaks one of these saturated
closures, then increases local reorder flexibility, and only later creates the
four-zero blocker run.

### Historical n=18 witness

For the 730 seeded bad type-states:

| distance | possible numbers of saturated blockers |
|---:|---|
| 1 | 4 through 9 |
| 2 | 6 through 9 |
| 3 | 9 |

The unique distance-three state has 12 blockers with deletion-ground closure
sizes

`5, 7, 7, 11, 11, 11, 11, 11, 11, 11, 11, 11`.

Thus 9 blockers attain the exact t=0 cap `3k-1=11`.

### Interpretation

This is not a monotonicity theorem.  Saturation count itself should **not** be
promoted to a descent potential.

The useful structural reading is instead:

> hard local states accumulate many rank-three flats that are already one
> element below the forbidden dangerous threshold.

A hypothetical component closed under all four-block repairs and pivots would
therefore have to maintain a highly saturated family of blocker closures.
The proof target should be to show that such persistent rigidity forces one
more element into one of these rank-three closures, producing a `3k`-element
set spanning the omitted element and contradicting the certified
`3k-1` cap.

This makes the desired implication more precise:

`closed all-bad local rigidity -> over-saturation -> dangerous hyperplane`.

## Fixed-e t=0 strengthening

A stronger t=0-specific experiment removes point pivots entirely.

For the complete binary represented n=10 class satisfying the exact
two-deletion caps (2,4,6):

- 28,476 multiplicity patterns;
- 16 GL(4,2) orbits;
- all 160 labelled pointed orbit representatives checked;
- move set: **only** arbitrary CBO-preserving permutations of four consecutive
  positions;
- omitted element held fixed throughout;
- **zero closed all-bad fixed-e components**;
- exact worst fixed-e distance to success: **4**.

So point pivots shorten some repair paths but are not needed for existence in
this entire exact class.

The dedicated certificate is:

`experiments/rank4_binary_n10_fixed_e_four_block_exact.py`

with compact result:

`experiments/rank4_binary_n10_fixed_e_four_block_exact_result.json`.

The same no-pivot formulation survived additional t=0 stress:

- n=14: 50 sampled bad states, distances 1:41 and 2:9;
- n=18: 35 sampled bad states, distances 1:28, 2:6, 3:1.

These larger-size checks are sampled, not exhaustive.

This suggests the t=0 branch may admit the stronger theorem:

> Fix any eligible omitted element e. Every connected component of the
> deletion-CBO graph under CBO-preserving four-block reorders contains a
> state into which e can be inserted.

Equivalently, no change of omitted element is needed.

This strengthening cannot hold uniformly for strict 4k: the strict binary
n=8 example already has prescribed elements with g(M,e)=0. Therefore the
**global existential favorable-state theorem may still unify strict 4k and
t=0, but the most promising move-based proof mechanism now appears
branch-specific**.

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

## Modular-cut interpretation and another dead potential

Fix an omitted element `e` and write `D = M \ e`.

Classically, the single-element extension from `D` back to `M` is encoded
by a modular cut: the flats `F` of `D` such that `e in cl_M(F)`.
This is the standard Crapo/Oxley correspondence between modular cuts and
single-element extensions (see Oxley, *Matroid Theory*, 2nd ed., §7.2).

In this language:

- a blocker triple is a consecutive independent triple whose closure lies in
  the modular cut;
- two overlapping blockers collapse to their shared pair because the relevant
  flats form a modular pair inside a basis window;
- three overlapping blockers collapse to the shared singleton;
- four would force the empty flat into the cut, i.e. make `e` a loop.

Thus the already-certified closure-intersection lemmas are exactly the local
modular-cut axioms needed by the proof, even though mathlib has no
`ModularCut` API.  There is currently no reason to build a full modular-cut
library; closure language is enough.

A second potential has now been falsified.

On the exact binary n=10 class, consider the multiset of sizes of the closures
of all blocker triples.  Bad states can be strict local maxima for:

- lexicographically sorted blocker-closure sizes;
- total blocker-closure size;
- number of maximum-size blocker closures followed by total size.

There are more than one thousand such bad local maxima in the exact orbit
audit.

The hardest fixed-e orbit gives a particularly clear example.  A distance-four
state has blocker word

`101110001`

and all five blocker closures have the maximum no-dangerous size 6.  Along a
shortest repair path the closure-size profile must first drop:

`(6,6,6,6,6) -> (6,6,6,6,4) -> ... -> success`.

So neither blocker count, run profile, nor blocker-closure concentration is a
universal monotone potential.

What survives is structural: long blocker runs encode very small spanning
sets.  In particular, a three-blocker run should be read as a parallel
obstruction (`e` is spanned by the single common element), and a two-blocker
run as a triangle-or-parallel obstruction (`e` is spanned by the common
pair).  This run-to-small-circuit classification is the next local geometry
worth exposing explicitly in Lean.

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


## Historical n=18 fixed-e move-family minimization

The fixed-e version of the historical n=18 witness was also used to ask
whether the proof really needs every nonidentity permutation in S4.

A six-type baseline was tested:

- the three adjacent transpositions inside a four-position block;
- `(2,3,0,1)`: `[a,b,c,d] -> [c,d,a,b]`;
- `(2,3,1,0)`: `[a,b,c,d] -> [c,d,b,a]`;
- `(3,1,2,0)`: `[a,b,c,d] -> [d,b,c,a]`.

With the omitted element fixed and no point pivots, this baseline repairs
725 of the 730 seeded bad type-states within depth 8 and leaves five failures.

Each of the remaining 17 S4 move types was then tested as one additional
generator. Exactly two symmetric involutions individually eliminate every
failure:

- `(0,3,2,1)`: `[a,b,c,d] -> [a,d,c,b]`;
- `(2,1,0,3)`: `[a,b,c,d] -> [c,b,a,d]`.

Using either one gives a seven-type fixed-e move family for which all 730
seeded bad states reach success, with maximum observed distance 6.

For either working seven-type family the repair histogram is:

- distance 1: 410;
- distance 2: 207;
- distance 3: 78;
- distance 4: 27;
- distance 5: 7;
- distance 6: 1.

The same seven-type family now also passes the **complete exact binary n=10** two-deletion-robust class: all 160 pointed orbit representatives have zero closed all-bad fixed-e components, and the exact worst repair distance remains 4, identical to the arbitrary-S4 audit. It also preserves the one-step repair behavior in the sampled sparse-paving n=14 stress.

This still does **not** justify replacing the arbitrary-S4 conjecture by the seven-type statement as a theorem; it is a proof-design simplification supported by the hardest historical stress example plus the complete exact binary n=10 census. In particular, the safest theorem
statement remains closure under arbitrary CBO-preserving four-block
permutations. But a constructive proof may only need adjacent exchanges plus
four nonadjacent local patterns.

Certificate:

`experiments/rank4_n18_fixed_e_move_family_minimization.py`

with compact result:

`experiments/rank4_n18_fixed_e_move_family_minimization_result.json`.

Exact n=10 companion certificate:

`experiments/rank4_binary_n10_fixed_e_seven_type_exact.py`

with compact result:

`experiments/rank4_binary_n10_fixed_e_seven_type_exact_result.json`.


## September 21 local-rigidity split

The local four-block analysis now separates cleanly into two different
matroid mechanisms.

### Transposition probes

Five of the seven empirically sufficient move types are transpositions:
the three adjacent swaps, the endpoint swap `(3,1,2,0)`, and the side swap
`(0,3,2,1)`.

Exact audits on the hard binary n=10 orbit show that these moves are often
useful primarily as **structural probes**, not direct repairs.

For omitted parallel labels 6 and 7:

- endpoint swap: 2,160 attempts per label, zero CBO-preserving;
  1,440 failures have an extreme-boundary witness and 720 are witnessed only
  at internal single-exchange boundaries;
- side swap: 2,160 attempts per label, zero CBO-preserving;
  1,328 failures have an extreme changed-boundary witness and 832 are
  internal-only.

Thus the skip-one three-element cores in the internal boundary windows are
genuinely necessary.  A proof using only the two consecutive-triple extreme
boundaries is insufficient.

Certificates:

- `experiments/rank4_binary_n10_endpoint_swap_obstruction_exact.py`;
- `experiments/rank4_binary_n10_endpoint_swap_obstruction_exact_result.json`;
- `experiments/rank4_binary_n10_side_swap_obstruction_exact.py`;
- `experiments/rank4_binary_n10_side_swap_obstruction_exact_result.json`.

The explicit endpoint-swap six-boundary geometry is Lean-green on
`rank4-seven-move-types` at `598b8257dd63d26b83c009a2e69ae875b8c849d8`
(workflow `35632709670`).

### Canonical 2+2 probes

The two canonical patterns have genuine double-exchange obstructions.

For the hard binary n=10 orbit:

- pair shift `(2,3,0,1)`: every attempt from every bad state is invalid;
- canonical twist `(2,3,1,0)`: some attempts are valid, including 120 per
  hard omitted parallel label;
- **both** patterns have failures witnessed only at the two double-exchange
  boundary windows.

Therefore single-element exchange/closure rigidity cannot close the
four-block argument.  The rank-two contraction/common-base layer is
mathematically necessary.

Certificate:

- `experiments/rank4_binary_n10_canonical_pairshift_obstruction_exact.py`;
- `experiments/rank4_binary_n10_canonical_pairshift_obstruction_exact_result.json`.

The generic four-element rigidity theorem already present in
`LocalRepairClosure.unique_local_repair_forces_ambient_closure` is the right
endpoint: uniqueness of the current common pair in the two boundary minors
forces one of four ambient closure incidences.

A finite wrapper reducing uniqueness to failure of the five explicit
alternative pairs is Lean-green on `rank4-five-pair-rigidity` at
`5b42fc9462486fe4f98e575c7272c0369bf10473`
(workflow `35634898131`).

## Saturated-flat constant defect

The saturation experiments suggest sharpening
`rigidity -> saturation -> oversaturation`.

Suppose a rank-three set `X` in a `4k+1` deletion CBO spans the omitted
element and attains the t=0 maximum

`|X| = 3k-1`.

Then its deletion-ground complement `C` has exactly

`|C| = k+2`.

Because `X` has rank at most three while every cyclic four-window is a
rank-four basis, every four-window meets `C`.

Now double-count incidences between complement positions and cyclic
four-windows.  Each element of `C` lies in exactly four four-windows, so the
total incidence count is

`4(k+2) = 4k+8`.

There are `4k+1` four-windows and each must contain at least one complement
position.  Therefore the total excess above one complement point per window
is exactly

`(4k+8) - (4k+1) = 7`.

Consequences:

- at most **seven** four-window starts contain two or more complement points;
- hence all but at most seven four-windows contain exactly one point outside
  `X`;
- in every such one-outside window, the other three entries are independent
  and rank three, hence form a basis of the saturated rank-three flat.

The equivalent cyclic-gap formulation is that runs inside `X` have length
at most three and the total deficit from the ideal length-three gaps is
exactly seven.

The key feature is that the defect bound is **independent of k**.  This turns
a potentially unbounded t=0 obstruction into a bounded exceptional
neighborhood plus a long forced `3+1` regime.

An isolated formalization is in progress on
`rank4-saturated-complement-interface` (draft PR #41).  It exposes the
rank-three-complement hits-every-four lemma, the exact `k+2` complement
cardinality, and a proposed `multiHitStarts_ncard_le_seven` theorem.

## Updated proof target

The current strongest proof architecture is:

1. work at fixed omitted element `e` in the no-dangerous t=0 deletion CBO;
2. assume a bad four-block component has no favorable state;
3. use the five transposition probes to extract single-exchange closure
   incidences;
4. use the two canonical 2+2 probes and five-pair common-base rigidity for
   the genuinely double-exchange cases;
5. force a blocker rank-three flat to the maximal allowed size `3k-1`;
6. use the constant-seven saturated-complement structure to obtain a long
   forced `3+1` regime;
7. show local rigidity in that regime pulls one further deletion element into
   the same rank-three closure;
8. obtain a rank-three `3k`-element set spanning `e`, contradicting the
   certified no-dangerous `3k-1` cap.

This remains a research program, not yet a proof of t=0.  In particular,
the missing theorem is still the propagation step from local move rigidity
to one saturated flat and then to one further forced closure element.
