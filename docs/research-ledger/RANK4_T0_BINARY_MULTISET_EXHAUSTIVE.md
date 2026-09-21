# Exact binary n=10 two-deletion lifting audit

Date: 2026-09-20

Branch: `rank4-t0-binary-multiset-exhaustive`.

Status: exact finite computation; **not Lean certification**.

## Goal

Stress-test the strongest t=0-specific insertion statement currently supported
by the theory:

> If a strict rank-four matroid on `4k+2` elements is universally robust under
> deleting any two elements, then every prescribed omitted element `e` has
> some deletion CBO of `M\e` into which `e` can be inserted.

For `n=10`, this is the first genuine `4k+2,t=0` size.

The certified theorem on branch `rank4-t0-two-deletion-robustness` shows that
strict `t=0` matroids satisfy the two-deletion hypothesis.  The question here
is whether that stronger hypothesis empirically removes the prescribed-element
counterexamples known under only one-deletion robustness.

## Exact represented family

The certificate

`experiments/rank4_t0_binary_multiset_exhaustive.py`

enumerates every multiplicity vector

`c in {0,1,2}^15`

of total weight 10 on the 15 projective points of `PG(3,2)`.

There are exactly **531,531** such multiplicity vectors.

For rank four at `n=10`, universal two-element deletion robustness is the
integer slack condition `s_j >= 2j`.  In the binary represented family this
is exactly the occupancy condition

- rank 1: `m_1 <= 2`;
- rank 2: `m_2 <= 4`;
- rank 3: `m_3 <= 6`.

These bounds already imply strict uniform density and exclude the dangerous
rank-three size-7 flat, so the surviving family is genuinely inside the
`t=0` regime.

Exactly **28,476** multiplicity vectors survive.

Their profiles are strikingly rigid:

| profile `(m1,m2,m3)` | configurations |
|---|---:|
| `(1,3,6)` | 2,163 |
| `(2,4,6)` | 26,313 |

The 2,163 simple examples are exactly the previously audited simple-binary
two-deletion-robust `n=10` class.  Every non-simple survivor has the saturated
profile `(2,4,6)`.

By number of doubled projective points, the robust family splits as:

| doubled points | configurations |
|---:|---:|
| 0 | 2,163 |
| 1 | 11,025 |
| 2 | 11,760 |
| 3 | 3,360 |
| 4 | 0 |
| 5 | 168 |

## GL(4,2) quotient

The 28,476 configurations split into only **16** `GL(4,2)` orbits.

Orbit-size distribution:

| orbit size | number of orbits |
|---:|---:|
| 105 | 1 |
| 168 | 2 |
| 315 | 1 |
| 420 | 2 |
| 840 | 3 |
| 1,680 | 1 |
| 2,520 | 3 |
| 5,040 | 3 |

The certificate chooses each orbit representative canonically.

## Exact insertion result

For every one of the 16 orbit representatives, the search treats parallel
copies as separately labelled elements and checks all 10 possible omitted
labels.

For each pointed state it searches all needed deletion CBOs until finding an
insertable one.  A returned witness is not accepted merely from the blocker
word: the resulting 10-element cyclic order is checked directly, window by
window, and every cyclic four-window must have binary rank four.

Result:

- pointed orbit-representative checks: **160**;
- prescribed-element failure orbits: **0**;
- existential failure orbits: **0**.

Coordinate isomorphisms transport the result across each `GL(4,2)` orbit,
and permutations of identical parallel copies transport it between copies of
the same projective point.  Hence the computation covers the entire exact
28,476-configuration family.

## Interpretation

This is substantially stronger evidence than the earlier simple-binary audit.

The known prescribed-element counterexamples under one-deletion robustness
do **not** survive the stronger two-deletion hypothesis in the complete binary
represented `n=10` class, even after allowing every parallel-pair pattern
compatible with strict density.

The strongest t=0-specific conjecture currently supported by computation is
therefore:

> **Two-deletion prescribed-element lifting conjecture.**
> Let `M` be a finite rank-four matroid of size `4k+2`, and assume every
> two-element deletion is uniformly dense and rank-preserving.  Then for every
> `e in E(M)`, some CBO of `M\e` admits insertion of `e`.

For the actual strict `t=0` branch, the certified two-deletion theorem would
supply the hypothesis automatically.

This conjecture is stronger than needed to close rank four and remains
unproved.  It must still be attacked outside the binary represented class,
especially with nonrepresentable matroids and larger `k`.
