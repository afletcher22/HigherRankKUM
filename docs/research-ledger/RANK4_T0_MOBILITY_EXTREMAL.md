# Rank-4 t=0 mobility-extremal program

Date: 2026-09-21.

Branch: `rank4-t0-mobility-extremal`.

Status: mathematical / computational research checkpoint.  No new endpoint in
this note is Lean-certified.

## Motivation

The one-step saturation conjecture is false: the explicit binary n=14 witness
on the parent branch has no favorable one-step four-block move and no saturated
rank-three flat through the omitted element, but repairs in two fixed-e moves.

What changes on the first move is not blocker count or blocker-closure size.
Instead, the order becomes much more locally reorderable.

This suggests using **mobility of the deletion CBO itself** as the extremal
quantity at the component level.

## Seven-move mobility

Use the seven local four-block permutations already isolated in
`Rank4/SevenMoveTypes.lean`:

1. the three adjacent transpositions;
2. `pairShift = (2,3,0,1)`;
3. `canonicalTwist = (2,3,1,0)`;
4. `endpointSwap = (3,1,2,0)`;
5. `sideSwap = (0,3,2,1)`.

For a deletion CBO `sigma`, define

`mu7(sigma)`

to be the number of pairs `(s,pi)`, where `s` is a cyclic start and `pi`
is one of the seven move types, such that applying `pi` to the four entries
starting at `s` gives another deletion CBO.

This counts **valid move attempts**, not distinct neighboring orders.  The
attempt count is preferable to graph degree because each summand is a local
basis predicate supported in a bounded neighborhood.

## Mobility-extremal saturation conjecture

Let `M` be a strict rank-four t=0 instance on `4k+2` elements, fix an
omitted element `e`, and let `sigma` be a CBO of `M \ e`.

Assume:

1. `sigma` is bad for insertion of `e`;
2. no seven-type CBO-preserving move from `sigma` is favorable;
3. for every bad seven-type CBO neighbor `tau`,
   `mu7(tau) <= mu7(sigma)`.

Then:

> `M` contains a rank-three flat `H` with `e in H` and `|H| = 3k`.

This is exactly the local extremal lemma needed for Astra's component
dichotomy.

Indeed, in a hypothetical closed all-bad fixed-e component, choose a state
maximizing `mu7`.  It automatically satisfies (1)--(3), hence the extremal
lemma produces the required saturated flat.

No monotone path theorem is required.

## Why this avoids the failed potentials

Earlier scalar potentials based on

- blocker count;
- zero-run profile;
- blocker-closure sizes;
- total closure concentration;

all fail because a shortest repair path may first make those quantities worse.

Seven-move mobility is different.  It measures how many **legal local
reorderings of the deletion CBO** are currently available.  The n=14
counterexample demonstrates the intended behavior:

- initial one-step-rigid bad state: `mu7 = 11`;
- there exists a bad seven-type neighbor with `mu7 = 14`;
- independently, a shortest seven-type repair has length two and score sequence
  `11 -> 11 -> 13`, with the last state favorable.

Thus one available bad move increases local reorder freedom.  Separately, the
shortest seven-type repair has length two but uses a different first move
(`mu7 = 11 -> 11 -> 13`, with the final state favorable).  So the evidence
supports an **extremal-state** argument, not a claim that every shortest repair
path monotonically increases mobility.

## Exact binary n=10 census

The complete two-deletion-robust binary n=10 class contains:

- 28,476 multiplicity patterns;
- 16 GL(4,2) orbits;
- 160 pointed orbit representatives.

Using only the seven move types:

- 6,004 bad states have no favorable seven-type neighbor;
- among these, 1,332 are local maxima of `mu7` among bad seven-type
  neighbors;
- **all 1,332 lie on a saturated 6-point rank-three flat through the omitted
  element**.

Of those 1,332 extrema:

- 1,232 already have a blocker triple whose closure is the saturated flat;
- 100 require indirect saturation geometry.

The local-max blocker-word distribution is:

- `001010111`: 416;
- `010101011`: 240;
- `000110111`: 144;
- `001011011`: 120;
- `000100101`: 112;
- `010110111`: 96;
- `011011011`: 88;
- `001100111`: 48;
- `001001011`: 24;
- `001011101`: 16;
- `000101011`: 8;
- `001010011`: 8;
- `001010101`: 8;
- `001001001`: 4.

Thus the exact finite census supports the mobility-extremal lemma, while the
stronger "visible blocker saturation" endpoint is false.

## Exact SQS(10) negative control

For the 30-circuit-hyperplane SQS(10) sparse-paving matroid, no rank-three
flat can be saturated at six points.

For a fixed omitted element:

- 9,024 deletion CBOs;
- 8,496 favorable states;
- 528 bad states.

Every one of the 528 bad states already has a favorable seven-type neighbor.
Hence there are **zero** bad seven-mobility local maxima.

This is an exact nonrepresentable-style negative control for the conjecture.

## Binary n=14 no-saturation stress

The explicit one-step counterexample matroid

`(10,3,11,1,3,3,15,15,6,6,1,14,11,7)`

has global rank-three flat maximum eight, so no omitted element can lie on a
saturated 9-point flat.

Among twelve sampled one-step-rigid bad states in this matroid, every state has
a bad seven-type neighbor of strictly larger `mu7`.

Examples of score increases include:

- `1 -> 5`;
- `4 -> 9`;
- `5 -> 11`;
- `10 -> 14`;
- `13 -> 24`;
- `25 -> 28`.

A further mutation stress produced nine additional one-step-rigid bad states
across nearby no-saturation binary n=14 matroids.  Again, every state had a
bad seven-type neighbor of strictly larger `mu7`.

No mobility-local-maximum counterexample without saturation has been found.

## Why the seven-type score is proof-friendly

The full S4 mobility score has the same empirical behavior, but the seven-type
score is preferable because the repository already contains the local geometry
for these probes:

- adjacent exchange closure;
- endpoint-swap six-boundary geometry;
- side-swap internal boundary witnesses;
- canonical 2+2 common-base rigidity;
- five-pair rank-two contraction rigidity.

Moreover, validity of one seven-type attempt is determined by only a bounded
set of rank-four windows.  If one four-block move changes the state, all
attempts far from the changed block retain the same validity.  Therefore the
difference

`mu7(tau) - mu7(sigma)`

is a bounded local calculation independent of `k`.

This is the key reason the extremal route may scale.

## Proposed proof architecture

1. Assume `sigma` is a bad local maximum of `mu7` with no favorable
   seven-type neighbor.
2. For each of the seven move types and each relevant local blocker pattern,
   classify:
   - move valid and bad;
   - move favorable;
   - move invalid with a specific failed boundary witness.
3. Use `mu7` maximality to rule out configurations where a valid bad move
   creates strictly more local move opportunities.
4. Translate the remaining failed probes into ambient closure incidences using
   the existing single-exchange and rank-two common-base lemmas.
5. Propagate those incidences around the cycle.
6. Show the surviving finite local patterns force a rank-three flat through
   `e` with `3k-1` deletion elements, hence `3k` total elements.

The desired global component theorem then follows by choosing a
`mu7`-maximal state in the component.

## Next concrete task

Formalize only the **locality of seven-move mobility**:

- define the seven-attempt validity predicate;
- define the local score at one cyclic start;
- define `mu7` as the sum of local scores;
- prove that a four-block reorder changes local scores only for starts within
  a bounded cyclic neighborhood.

Do not yet formalize the extremal saturation theorem.

In parallel, computationally enumerate the possible local score changes for
the seven move types on the existing hard binary witnesses.  The goal is to
extract a finite list of "score-nondecreasing or closure-obstruction" local
rules suitable for a representation-free proof.
