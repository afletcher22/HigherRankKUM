# Exact binary strict n=12 lifting audit

Date: 2026-09-20

Branch: `rank4-strict4k-binary-n12-exhaustive`.

Status: exact finite computation; **not Lean certification**.

## Goal

Stress-test the remaining strict `4k` branch at the first nontrivial size
`n=12`, without imposing the stronger two-deletion hypothesis available in
the `t=0` branch.

The relevant candidate statement is stronger than needed:

> For every prescribed element `e` of a strict rank-four matroid on 12
> elements, there is some CBO of `M\e` into which `e` can be inserted.

The general prescribed-element theorem is false at `n=8`, so this audit asks
whether the obstruction persists once the strict integral branch reaches
`k=3`.

## Complete binary represented class

Every loopless binary rank-four matroid is represented by multiplicities on
the 15 nonzero projective points of `PG(3,2)`.

For `n=12`, strict density forces projective multiplicity at most two.  Thus
the certificate

`experiments/rank4_strict4k_binary_n12_exhaustive.py`

exhausts the entire binary strict class by enumerating every vector
`c in {0,1,2}^15` with total weight 12.

There are **1,161,615** such multiplicity vectors.

For rank four on 12 elements, strict uniform density is exactly the occupancy
condition

- rank 1: `m_1 <= 2`;
- rank 2: `m_2 <= 5`;
- rank 3: `m_3 <= 8`.

Exactly **610,295** configurations satisfy these bounds.

Their exact profile distribution is:

| profile `(m1,m2,m3)` | configurations |
|---|---:|
| `(1,3,6)` | 35 |
| `(1,3,7)` | 420 |
| `(2,4,7)` | 47,460 |
| `(2,4,8)` | 69,300 |
| `(2,5,8)` | 493,080 |

By number of doubled projective points:

| doubled points | configurations |
|---:|---:|
| 0 | 455 |
| 1 | 15,015 |
| 2 | 117,495 |
| 3 | 264,600 |
| 4 | 187,110 |
| 5 | 25,200 |
| 6 | 420 |

Only **47,915** of the 610,295 strict configurations satisfy universal
two-element deletion robustness.  Hence **562,380** strict examples in this
audit lie outside the stronger hypothesis used for the `t=0` branch.

## GL(4,2) quotient

The 610,295 configurations split into only **85** `GL(4,2)` orbits.

Orbit-size distribution:

| orbit size | orbits |
|---:|---:|
| 35 | 1 |
| 210 | 1 |
| 315 | 2 |
| 420 | 2 |
| 840 | 3 |
| 1,260 | 3 |
| 1,680 | 1 |
| 2,520 | 13 |
| 3,360 | 7 |
| 5,040 | 18 |
| 10,080 | 23 |
| 20,160 | 11 |

The certificate chooses canonical orbit representatives.

## Exact lifting result

For each of the 85 orbit representatives, parallel copies are retained as
separately labelled elements.  Every one of the 12 possible omitted labels is
tested.

For each pointed deletion, the search enumerates deletion CBOs as needed until
it finds an insertable order.  Every proposed full 12-element order is checked
directly: all cyclic four-windows must have binary rank four.

Result:

- pointed orbit-representative checks: **1,020**;
- prescribed-element failure orbits: **0**;
- existential failure orbits: **0**.

Coordinate isomorphisms and permutations of parallel copies transport these
witnesses across the entire exact class.  Thus every prescribed element is
favorable in every binary strict rank-four matroid on 12 elements.

## Interpretation

This is stronger than the corresponding `t=0` binary result in one important
sense: most of the strict `n=12` class is **not** two-deletion robust.
Therefore the observed favorable lifting cannot be explained merely by the
extra t=0 deletion slack.

The data now separate the known `n=8` prescribed-element obstruction from
the first larger strict integral case:

- strict binary `n=8`: prescribed-element failure occurs in one substantial
  orbit;
- strict binary `n=12`: no prescribed-element failure anywhere in the
  complete class.

This is evidence that the `n=8` obstruction may be a small-boundary
phenomenon rather than the generic strict-`4k` behavior.  It is **not**
enough to assert a universal every-element theorem for strict `4k`.

The safe cross-branch target remains the existential favorable-state theorem.
For the `t=0` branch, the stronger two-deletion prescribed-element lifting
statement remains especially plausible.
