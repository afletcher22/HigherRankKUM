# Rank-4 t=0 forced-component audit

Date: 2026-09-20

Branch: `rank4-t0-forced-component-audit`.

Status: exact finite GF(2) computation for one fixed witness; **not Lean certification**.

## Scope

This extends the existing 18-element strict rank-four `t=0` two-step repair
witness from `RANK4_T0_TWO_STEP_OBSTRUCTION.md`.

Rather than enumerate the enormous full repair component, the new certificate

`experiments/rank4_t0_forced_component_audit.py`

restricts to the forced-unorientable subgraph.  For odd `N=9`, these are the
states whose local relation masks are all Boolean bijections and have odd
forced parity.  Every edge is a legal local `2+2` repartition.

The committed output is

`experiments/rank4_t0_forced_component_result.json`.

## Exact result

The forced component containing the displayed initial witness has exactly
**144 states**.

Of these:

- **136** have an immediate legal repair that creates Boolean slack and is
  directly orientable;
- exactly **8** have no immediate orientable/slack repair.

The eight exceptional states are not a diffuse plateau.  Their induced
forced-preserving graph is exactly the 3-dimensional cube `Q_3`:

- 8 vertices;
- 12 induced edges;
- degree 3 at every core vertex;
- bipartition sizes 4 and 4;
- ordered distance counts `0:8, 1:24, 2:24, 3:8`.

Every cube vertex also has six forced-preserving edges leaving the cube, for
48 core-to-boundary edges in total.  Every such boundary state has an
immediate orientable/slack repair.  Therefore every core state is exactly one
forced move from an escape-capable forced state, and two repairs from an
orientable state.

For this fixed witness the apparent two-step obstruction is therefore an
eight-state rigid core with a very explicit boundary.

## Closure potential does not explain the core

The exact joint distribution
`(closurePotential, forced degree, immediate escape count, forced distance
to escape-capable)` is:

| tuple | states |
|---|---:|
| `(6,9,0,1)` | 8 |
| `(6,3,3,0)` | 8 |
| `(8,5,3,0)` | 48 |
| `(8,3,4,0)` | 24 |
| `(10,2,6,0)` | 24 |
| `(10,3,4,0)` | 24 |
| `(12,3,3,0)` | 8 |

Thus the rigid core happens to sit at closure potential 6, but potential 6
also occurs in escape-capable states.  Higher closure potential does not mean
farther from escape.  This is consistent with the earlier failure of pure
closure-potential ascent.

## Structural interpretation

Inside the rigid core, the three cube directions are independent
forced-preserving wholesale swaps of disjoint local pair choices.  Moving
along a cube edge preserves the obstruction.  A cross repair exits the rigid
core into one of the 136 forced states that has a slack-creating repair.

This suggests a more specific proof shape for the pair-cycle route:

> classify a forced state with no immediate slack exit, and show either that
> it already contradicts strict density or that a forced-preserving move
> leaves the rigid class.

For the present witness the second alternative occurs after one move.

This is only evidence from one exact component.  It does **not** justify a
universal repair-distance-two theorem.

## Relation to the favorable-state program

The pair-cycle repair graph remains a stronger object than the existential
`(e,sigma)` favorable-state problem.  The value of this audit is therefore
diagnostic: it shows that the historical two-step obstruction has a small,
structured low-rank core rather than a large featureless plateau.

The next formal lemma should still be the representation-free blocker
closure/intersection package recommended by the deletion-insertion report.
It connects local bad-run geometry directly to low-rank closure
concentrations without assuming a monotone potential.
