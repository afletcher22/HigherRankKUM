# Rank-4 t=0 finite-radius research

Date: 2026-09-21.

Branch: `rank4-t0-radius3-research`.

Status: mathematical / computational research checkpoint.  **All constant-radius
shortcuts tested here are false.**  Explicit no-saturation witnesses now have
exact repair distances 3, 4, 5, 6, and 8 as k grows from 3 to 7.

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

## Radius three and constant-radius variants: false

The radius-three strengthening also fails.

Starting from the radius-two counterexample and repeatedly adjoining a
four-element basis block while preserving the t=0 caps produced the following
explicit binary witnesses:

| k | n=4k+2 | exact fixed-e four-block distance | ambient flat profile |
|---:|---:|---:|---:|
| 3 | 14 | 3 | (3,5,9) |
| 4 | 18 | 4 | (4,7,12) |
| 5 | 22 | 5 | (5,9,15) |
| 6 | 26 | 6 | (6,11,17) |
| 7 | 30 | 8 | (6,12,20) |

For every row:

- the displayed deletion order is a rank-four CBO;
- every two-element deletion retains rank four;
- the two-deletion density caps `(k,2k,3k)` hold;
- the omitted element lies on **no** saturated `3k`-point rank-three flat;
- the distance is exact under arbitrary CBO-preserving permutations of four
  consecutive positions with the omitted element fixed.

The n=30 witness in particular survives seven layers of bad states and first
reaches success at distance eight.

Executable certificate:

`experiments/rank4_t0_growing_radius_witnesses.py`.

These data do not yet prove an unbounded family, but they decisively eliminate
radius 3 and make any universal constant-radius theorem implausible.

## Structural interpretation

The witnesses are obtained by extending a hard state with remote four-element
basis blocks.  Transient rigidity can therefore be **stacked**: a local repair
must propagate through several separated regions before any four-zero blocker
run appears.

This is exactly the phenomenon a true component proof must tolerate.  A
bounded-depth theorem cannot replace the component hypothesis.

The next research question is whether this extension mechanism can be proved
as an infinite family:

> given a no-saturation witness of distance d, can one adjoin a four-element
> basis gadget preserving strict/two-deletion robustness and force distance at
> least d+1?

Even a partial extension lemma would be useful diagnostically, but it is not
needed for the rank-4 proof itself.

## Live proof target

Return to Astra's component-level statement:

> in the no-dangerous t=0 branch, a fixed-e four-block component that contains
> no favorable state forces a saturated rank-three flat through e.

The growing-radius family shows why the proof must use **closure under the
whole component**, not any bounded neighborhood of one state.

