# Rank-4 t=0 finite-radius research

Date: 2026-09-21.

Branch: `rank4-t0-radius3-research`.

Status: mathematical / computational research checkpoint.  Radius two is
**false**.  Radius three remains only a falsification target, not a theorem.

## Motivation

The exact one-step saturation selector is false, and the stronger statement

`no saturated rank-three flat through e => one-step repair`

is also false.

The next natural strengthening was to ask whether absence of a saturated flat
forces a uniformly short fixed-e four-block repair path.

## Radius-two conjecture: false

There is an explicit binary n=14 counterexample:

`(10,3,11,1,3,3,15,15,7,6,1,14,11,7)`

with omitted label `e=10` and deletion CBO

`(0,7,1,8,11,9,4,13,12,3,6,5,2)`.

The state has blocker word

`0001010111011`.

It satisfies the full intended t=0 robustness package:

- ambient rank 4;
- flat profile `(3,5,9)`;
- every two-element deletion retains rank 4;
- every two-element deletion satisfies the 12/4 density caps;
- no 9-point rank-three flat contains the omitted element.

Nevertheless:

- the state is bad;
- no single arbitrary CBO-preserving four-block reorder is favorable;
- no state reachable in two such moves is favorable;
- the exact fixed-e distance to success is **3**.

One shortest path has blocker words

`0001010111011`
→ `0011010111011`
→ `0011000111011`
→ `0010000111011`,

with the final state favorable.

Executable certificate:

`experiments/rank4_binary_n14_radius_two_counterexample.py`.

Thus

`no saturation => radius <= 2`

is false.

## Radius three: current evidence only

Radius three has not been falsified in the no-saturation regime.

The following evidence is currently available.

### Existing repository evidence

- Exact hard binary n=10 orbit:
  every distance-3 state has all blocker closures saturated.
- Historical binary n=18 stress:
  the unique distance-3 sampled state has nine saturated blocker closures.
- Historical binary n=14 stress:
  the unique sampled distance-3 state omits an element lying on a 9-point
  rank-three flat.
- Odd-field n=10 no-saturation pointed audits:
  every bad state was one-step repairable.
- Sparse-paving n=14 no-saturation-style stress:
  every sampled bad state was one-step repairable.

### New mutation stress

Starting from the explicit n=14 no-saturation witnesses and mutating one to
three columns while retaining the binary rank-4/two-deletion caps:

- first sweep: 3,461 qualifying matroids, 667 bad states, 52 one-step-rigid
  states, one state surviving depth two, zero states surviving depth three;
- second sweep: 6,199 qualifying matroids, 1,263 bad states, 130 one-step-rigid
  states, five states surviving depth two, zero states surviving depth three.

Combined:

- 9,660 qualifying nearby matroids;
- 1,930 bad sampled states;
- 182 one-step-rigid states;
- six states requiring at least three moves;
- **zero** observed no-saturation states requiring more than three moves.

This is meaningful falsification evidence, but nowhere near a proof.

## Why radius three would be valuable

If the following were true,

> every bad t=0 deletion CBO with no saturated `3k`-point rank-three flat
> through e reaches a favorable state in at most three arbitrary four-block
> moves,

then Astra's full component dichotomy would follow immediately.

More importantly, a three-step theorem is still local enough to attack by
explicit boundary geometry:

- one move changes a bounded neighborhood;
- two moves involve only a bounded union of neighborhoods;
- three failed repair layers produce a finite family of failed boundary
  basis tests;
- the existing closure-intersection and rank-two common-base lemmas can turn
  those failures into closure incidences.

This is materially more concrete than an arbitrary-component theorem.

## Caution

Do not promote radius three to a formal target yet.

Earlier research repeatedly found finite-radius statements that survived broad
sampling before failing on structured examples.  The correct next step is
adversarial falsification, especially:

1. mutate the new distance-3 witness while preserving no saturation;
2. search cap-heavy binary n=18 instances;
3. search representable odd-field n=14/n=18 instances with parallel classes;
4. search sparse-paving/nonrepresentable instances designed to suppress local
   four-block freedom.

Only if radius three survives those tests should we spend Lean effort on a
three-layer local theorem.

## Relation to the full component theorem

Even if radius three eventually fails, these witnesses are useful.

They show a hierarchy:

- one-step rigidity can be transient;
- two-step rigidity can also be transient;
- each additional layer of transient rigidity appears to require more
  saturated/near-saturated closure geometry.

That supports Astra's component-level intuition: persistent rigidity across an
entire component should force saturation, even though any fixed shallow layer
may fail.
