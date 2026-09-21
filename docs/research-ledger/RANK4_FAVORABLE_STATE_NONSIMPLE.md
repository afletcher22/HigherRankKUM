# Rank-4 favorable states — non-simple represented audit

Date: 2026-09-20/21.

Branch: `rank4-favorable-state-nonsimple`.

Status: finite computation only; no Lean certification is claimed here.

## Exact binary n=10 census

The new certificate

`experiments/rank4_binary_n10_nonsimple_exact.py`

enumerates every multiplicity vector

`c in {0,1,2}^15`

of total size 10 on the 15 nonzero points of `PG(3,2)`.  The exact universal
two-deletion density caps are

- rank 1: at most 2 elements;
- rank 2: at most 4 elements;
- rank 3: at most 6 elements.

Exactly **28,476** multiplicity patterns satisfy these caps.  Their
distribution by number of doubled projective points is

| doubled points | patterns |
|---:|---:|
| 0 | 2,163 |
| 1 | 11,025 |
| 2 | 11,760 |
| 3 | 3,360 |
| 4 | 0 |
| 5 | 168 |

Quotienting by `GL(4,2)` gives exactly **16 orbits**.

Every labelled omitted element was checked on one representative of every
orbit.  Every one admits at least one deletion CBO into which it can be
reinserted.  Thus the stronger t=0-specific prescribed-element lifting
conjecture survives the complete non-simple binary n=10 represented class.

This strictly extends the earlier simple-binary census: parallel pairs and
larger allowed parallel structure are now included.

## Closed all-bad components exist

The same 16 orbit representatives were exhaustively audited as joint state
graphs `(e,sigma)`.

With moves consisting of adjacent CBO-preserving swaps plus point pivots,
**5 of the 16 orbits** contain closed all-bad components.  Across those five
representatives there are 104 such components.

Therefore the proposed statement

> every state component contains a successful state

is false even under universal two-deletion robustness.

The obstruction is not merely caused by insisting on adjacent swaps.  If one
allows **every single transposition** of the deletion CBO that preserves the
CBO, together with point pivots, one orbit still has:

- 4,128 states;
- 1,856 successful states;
- 9 connected components;
- **8 closed all-bad components**, each of size 4.

For a state in one such component, the nearest successful CBO found with the
same omitted element differs in four positions.  Thus any universal local
escape theorem would need a genuinely larger move than one transposition, or
a different state space.

This kills the natural component-wise proof strategy but does **not** threaten
the global favorable-state conjecture: every omitted element in the same
matroid still has a successful state elsewhere.

## Seeded odd-field non-simple stress

Independent seeded stress tests were also run on represented multisets with
genuine parallel classes.

No prescribed-element failures were found in:

- 100 qualifying GF(3), n=10 examples;
- 60 qualifying GF(5), n=10 examples;
- 40 qualifying binary, n=14 examples;
- 40 qualifying GF(3), n=14 examples;
- 30 qualifying GF(5), n=14 examples.

The n=14 sample includes examples attaining the two-deletion flat caps, e.g.
occupancy profile `(3,6,9)`.

These odd-field and n=14 checks are sampling evidence, not exhaustive
certificates.

## Relation to sparse-paving stress

The companion sparse-paving experiment on the favorable-state branch gives
non-coordinate/nonrepresentable-style evidence at n=10: the extremal
30-circuit-hyperplane SQS(10) case and 1,000 seeded dense sparse-paving
samples also showed no prescribed-element failure.

Taken together, the current evidence for the t=0-specific theorem is much
broader than representable simple matroids.

## Updated proof-strategy lesson

The strongest computationally supported t=0 statement is now:

> universal two-deletion robustness may imply favorable lifting for every
> prescribed element.

By contrast, the following move-based strengthening is false:

> every unsuccessful state can reach success inside its component under
> adjacent swaps and point pivots,

and remains false even when arbitrary single transpositions are added.

The next proof target should therefore be a **global existence/selection
lemma for deletion CBOs**, not a universal local descent or component
connectivity theorem.

The green blocker-geometry branch supplies the right local language:
blockers are contraction dependencies, overlapping blocker runs collapse by
closure intersection, and blocker fundamental circuits persist across
sliding basis windows.  The next formal adapter should package these facts
for a cyclic deletion CBO and prove the no-four-consecutive-blockers theorem.
