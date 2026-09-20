# Rank-4 favorable-state research after t>0 certification

Date: 2026-09-20

This ledger records the first post-t>0 falsification pass. It distinguishes
Lean certification from finite computation.

## Certified starting point

On `rank4-density-slack-continuation`, commit
`0fb9fa5971158d8a4dc4972231287884ce1c3ac1` has full green root CI.
The unified positive-dangerous-hyperplane theorem
`exists_cbo_of_dangerous_hyperplane` is active on the root import path.
The single-deletion t=0 package is also active and green there.

## Surviving central conjecture

For a strictly uniformly dense rank-4 matroid of even size at least 8, if
every single-element deletion is uniformly dense and rank-preserving, there
exists an omitted element e and a CBO of M\e into which e can be inserted.

Equivalently, the joint state space contains at least one blocker word with
a cyclic nonblocker run of length at least four.

This remains conjectural.

## Exact simple-binary audit

The experiment
`experiments/rank4_favorable_state_falsification.py` exhausts every
universally deletion-robust simple binary rank-4 representation of even size
inside PG(3,2). Since PG(3,2) has 15 points, n=8,10,12,14 are the complete
possible even sizes >=8 for simple binary rank 4.

Results:

| n | qualifying matroids | pointed deletions | matroids with prescribed-e failures | existential failures |
|---|---:|---:|---:|---:|
| 8  | 3375 | 27000 | 840 | 0 |
| 10 | 2163 | 21630 | 0 | 0 |
| 12 | 455  | 5460  | 0 | 0 |
| 14 | 15   | 210   | 0 | 0 |
| total | 6008 | 54300 | 840 | 0 |

For n=8, each of the 840 exceptional matroids has exactly one bad prescribed
element. Thus the known strict-eight counterexample is part of a substantial
but tightly bounded phenomenon: fixed-e insertion can fail, yet element
selection always rescues the entire simple-binary class.

This is exact finite computation, not Lean certification.

## Nonbinary stress test

Seeded universally deletion-robust simple samples were tested at GF(3) and
GF(5), n=12 and n=14, 20 accepted matroids per field/size pair. Across 1,040
pointed deletions, every prescribed element had a favorable state.

This is seeded evidence only, not exhaustive.

## Joint-state graph and run-profile potential

States are pairs (e,sigma), where sigma is a deletion CBO of M\e.
Moves are:
1. cyclic adjacent swaps preserving the deletion CBO;
2. point pivots replacing an entry f by e whenever the resulting order is a
   CBO of M\f.

Let lambda be the descending tuple of cyclic nonblocker-run lengths.

Exact audits reproduce:

* strict eight-element witness: 432 states, one connected component,
  144 successful states;
* t=0 n=10 g=1 witness: 4224 states, one connected component,
  1920 successful states.

However the lexicographically nondecreasing run-profile escape conjecture is
false already in the strict-eight example. There are exactly 48 unsuccessful
states of profile (3,1) which are local maxima. A representative is

```
omitted label 0
order (1,2,4,3,7,6,5)
blockers 0110001
profile (3,1)
```

Its only neighboring profile is (2,2). Thus any escape must initially reduce
Lmax from 3 to 2. An explicit shortest successful profile path is

```
(3,1) -> (2,2) -> (3,1) -> (6)
```

Therefore both of the following are false for the unified rank-4 regime:

* every unsuccessful state has a nondecreasing lexicographic run-profile path
  to success;
* every local maximum of Lmax below 4 forces a forbidden density
  concentration.

By contrast, every state in the t=0 n=10 witness does have nondecreasing
run-profile escape. This may still indicate extra structure specific to t=0.

## Connectivity is also too strong

A qualifying simple binary n=8 example with columns

```
(1,3,4,6,8,10,13,15)
```

has 384 states and 384 connected components under adjacent swaps plus point
pivots: every state is isolated. All 384 states are successful.

Hence global state-graph connectivity is not the right theorem. The relevant
weaker target is absence of a closed all-bad component.

The complete qualifying simple-binary n=8 class was then audited exactly.
Across all 3,375 matroids there is no closed all-bad component. The state
graphs fall into exactly three metric classes:

* 2,520 matroids: 384 states, one component, monotone run-profile escape from
  every state, required Lmax drop 0;
* 840 matroids: 432 states, one component, exactly 48 states without
  lexicographically nondecreasing profile escape, maximum required Lmax drop 1;
* 15 matroids: 384 states, 384 isolated components, all states successful.

Thus the weaker bounded-valley statement `Lmax drop <= 1` is exact for the
entire simple-binary n=8 class, and the no-closed-all-bad-component statement
also survives exactly there.

The 3,375 qualifying n=8 representations split into exactly three
`GL(4,2)` orbits, and these orbit sizes coincide with the three state-graph
classes:

* orbit size 2,520: four triangles, 384 states, connected, monotone escape;
* orbit size 840: three triangles, 432 states, connected, 48 profile-local
  obstructions and required `Lmax` drop exactly one;
* orbit size 15: no triangles, 384 isolated states, every state successful.

The size-15 orbit consists of complements of projective hyperplanes (the
8-point affine-cube type). The size-840 orbit is exactly the prescribed-e
failure class from the favorable-state audit: a representative is
`(7,8,10,11,12,13,14,15)`, whose unique bad element is 7. Its three
triangles are
`(7,8,15)`, `(7,10,13)`, and `(7,11,12)`.
Thus six of the seven other points are paired by lines through the bad
element. This gives a concrete rank-2 geometric source for the run-profile
valley.

## Structural interpretation of the strict8 plateau

In the local-maximum witness above, the two consecutive blockers collapse to
the shared pair by the closure-intersection lemma. In the binary
representation this is a triangle through the omitted element. Thus the
plateau is supported by genuine rank-2/triangle geometry, not by a dangerous
rank-3 hyperplane. This explains why t=0/integral deletion robustness alone
does not make an Lmax ascent argument work.

A possible restricted direction is to ask whether paving/simple-without-
triangles hypotheses eliminate these valleys, but that would not by itself
close general rank 4.

## New formal structural target

On isolated branch `rank4-t0-two-deletion-robustness`, the proposed module
`HigherRankKUM/Rank4/T0TwoDeletion.lean` formalizes:

1. under strict 4k+2 density and no dangerous hyperplane, every rank-at-most-3
   set has size at most 3k;
2. for k>=2, deleting any two ground elements preserves size 4k, rank 4, and
   uniform density.

This is strictly stronger deletion robustness in the t=0 branch. It should be
treated as structural infrastructure, not as an insertion theorem.

That isolated branch is now certified: commit
`56644c48b9ddd9f9249058c76907f07433a74cc4` passed the full root CI build.
This does not mean it has been merged into the shared research branch.

## Exact simple-binary two-deletion filter

The stronger t=0-specific target

> every element is favorable under universal two-element deletion robustness

gets a substantially cleaner exact binary test than the one-deletion theorem.

Using the exact slack condition `s_j >= 2j`, the complete strict simple-binary
rank-four classes inside `PG(3,2)` split as follows:

| n | strict simple-binary matroids | two-deletion robust | prescribed-e failures inside robust class |
|---|---:|---:|---:|
| 8  | 3,375 | 15 | 0 |
| 10 | 3,003 | 2,163 | 0 |
| 12 | 455 | 455 | 0 |
| 14 | 15 | 15 | 0 |

Thus all **2,648** two-deletion-robust simple-binary matroids in the complete
even-size range, comprising **27,420 pointed deletions**, are favorable for
every omitted element.

At n=8 the filter is especially revealing.  The 3,360 strict examples with
profile `(m1,m2,m3)=(1,3,5)` fail two-deletion robustness.  The only 15
survivors have profile `(1,2,4)`; they are exactly the affine-cube orbit
identified above, whose 384 joint states are all successful.  In particular,
the entire 840-member prescribed-e failure orbit is excluded by the
two-deletion hypothesis.

At n=10 the split is similarly sharp: 2,163 examples have profile `(1,3,6)`
and are two-deletion robust, while the remaining 840 have profile
`(1,3,7)` and fail the two-deletion inequality in rank three.

This is exact finite computation for simple binary representations, not a
Lean theorem and not evidence about all nonrepresentable matroids.

## Current falsification status

Dead:
* prescribed-e favorable deletion in the full strict-even class;
* g>=2;
* blocker-count descent/minimization;
* monotone lexicographic nonblocker-run profile;
* monotone Lmax;
* universal joint-state connectivity.

Still alive:
* existential favorable-state conjecture;
* no closed all-bad component under adjacent swaps + point pivots;
* bounded-valley escape (exactly drop <=1 throughout the complete qualifying
  simple-binary n=8 class);
* stronger prescribed-e statement specific to tested t=0 instances.

## Next priorities

1. Continue nonbinary n=12/n=14 falsification, especially structured GF(3)
   and GF(5) families rather than only random samples.
2. Search explicitly for a closed all-bad state component.
3. Test bounded-valley escape and identify the geometry of states requiring
   an Lmax drop.
4. Separate t=0-only statements from the unified strict-4k / t=0 theorem.
5. If the two-deletion Lean package becomes green, use it as a formal
   hypothesis source for t=0-specific exchange lemmas.
