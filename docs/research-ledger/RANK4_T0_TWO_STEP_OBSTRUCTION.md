# Rank 4 t=0: two-step repair obstruction

Date: 2026-09-19.

Branch: `rank4-density-slack-continuation`.

## Result

The strengthening

> every strict rank-four `4k+2` matroid with no dangerous hyperplane
> has every obstructed admissible pair cycle one cross repair away from
> relation orientability

is false.

A fixed binary rank-four example on 18 labelled elements has no dangerous
rank-three hyperplane, yet the displayed admissible nine-pair cycle is forced,
has odd relation parity, and has no one-step orientable local `2+2`
repartition.  It does, however, reach an orientable pair cycle in exactly two
cross repairs.

This is a guardrail against treating the `t=0` branch as a one-step escape
theorem.  It is not a counterexample to KUM.

## Exact witness

The labelled nonzero vectors of `GF(2)^4`, written in four-bit integer
encoding, are

```
(1,2,4,8,9,6,2,8,1,4,3,12,1,8,2,4,5,10).
```

The initial pair cycle is

```
(0,1) (2,3) (4,5) (6,7) (8,9) (10,11) (12,13) (14,15) (16,17).
```

Exact subset enumeration gives rank 4 and maximum proper-set cardinalities

| rank | maximum size |
|---:|---:|
| 1 | 3 |
| 2 | 7 |
| 3 | 12 |

For `n=18=4*4+2`, strict density permits at most `4,8,13` elements at
ranks `1,2,3` respectively, with equality at rank 3 defining a dangerous
hyperplane.  Thus the example is strictly uniformly dense and has
`t=0`.

The initial local relation masks are

```
(9,9,9,9,9,9,9,6,9).
```

All are Boolean bijections and the forced parity is odd, so the pair cycle is
not relation-orientable.

## Exhaustive one-step check

At every one of the nine repair boundaries there is exactly one nonidentity
legal `2+2` repartition.  Exhausting all nine possibilities gives zero
orientable targets.  Hence the repair distance is greater than one.

This refutes both of the following proposed routes:

1. `t=0` implies a one-step escaping repair;
2. failure of all one-step escapes implies a dangerous hyperplane.

## Two-step certificate

One legal first repair gives

```
(0,1) (2,3) (4,5) (6,7) (8,11) (9,10) (12,13) (14,15) (16,17)
```

with forced masks

```
(9,9,9,6,9,6,9,6,9).
```

It is still unorientable.  A second legal cross repair gives

```
(0,1) (2,3) (4,6) (5,7) (8,11) (9,10) (12,13) (14,15) (16,17)
```

with masks

```
(9,9,9,14,9,6,9,6,9).
```

The mask `14` has Boolean slack.  A satisfying orientation is

```
(1,1,1,1,1,1,1,0,1),
```

which flattens to the labelled cyclic order

```
(1,0,3,2,6,4,7,5,11,8,10,9,13,12,14,15,17,16).
```

Every cyclic four-window of this order is independently rank-checked as a
basis.

The executable certificate is
`experiments/rank4_t0_two_step_repair_certificate.py`, with committed output
`experiments/rank4_t0_two_step_repair_result.json`.

## Consequence for the proof strategy

The remaining `t=0` branch is genuinely a multi-step or favorable-choice
problem.  The current formal cross-repair parity theorem still gives an
important reduction: a forcedness-preserving cross repair cannot change
relation orientability, so every eventual escape must occur at a step that
creates local Boolean slack.

The next target should therefore be one of:

- a bounded or finite reachability theorem for `t=0`;
- a new bounded potential / lexicographic invariant on forced states;
- an existential favorable deletion-CBO theorem, rather than insertion into
  an arbitrary deletion CBO.

Closure potential alone is already known insufficient for strict monotone
ascent, and this witness shows that direct one-step slack is also insufficient.

A useful computational next step is to enumerate the entire repair component
of this fixed `t=0` matroid and compare candidate state statistics against
distance to the orientable region.  In particular, test combinations of
closure potential, local forced-mask pattern, number of legal cross moves,
and local closure/parallel-incidence data before committing to a new formal
potential.

## Guardrails

Do not infer from this example that every `t=0` obstruction is at distance
two.  The certificate establishes only this fixed witness.

Do not infer that dangerous hyperplanes are irrelevant.  They remain the
correct deletion obstruction and are handled by separate direct constructions
for `t=1,2,3`.

Do not revert to the statement that every deletion CBO is insertable.  That
stronger insertion claim has separate counterexamples even when `t=0`.
