# Generalization Status

This file distinguishes certified generic infrastructure from rank-specific results and open research targets.

## Status vocabulary

- **Formalized generic** — Lean theorem has no fixed ambient-rank hypothesis and lives in the HigherRankKUM generic dependency chain.
- **Formalized conditional** — Lean theorem is generic but assumes lower-rank KUM solvers or other hypotheses not yet supplied internally by this repo.
- **Internalization pending** — a result is certified in the source project, but HigherRankKUM does not yet contain its own internal certified implementation.
- **Research target** — no formal proof is currently present in HigherRankKUM.

## Formalized generic infrastructure

The following has been migrated from the Rank3KUM higher-rank exploration and separated from rank-three-specific imports:

- `UniformlyDense` and `Tight`.
- Uniform-density inheritance under restriction.
- Tight sets are flats in finite uniformly dense matroids.
- Uniform density excludes loops.
- `cyclicIndex`, `cyclicWindow`, and arbitrary-rank `CyclicBasisOrder`.
- Rank formula relating a set and its contraction.
- Lifting restriction/contraction bases to a basis of the original matroid.
- Uniform-density inheritance under contraction by a finite tight set.
- Abstract restriction/contraction window gluing.
- Balanced `(L^s R^t)^k` interleaving and cyclic-window decomposition.
- Concrete arbitrary-rank balanced restriction/contraction gluing.

## Formalized conditional induction

`SolvesDivisibleKUMAtRank α r` records the divisible KUM statement at rank `r`:

- ambient rank `r`;
- ground size exactly `r * k`;
- uniform density with parameter `k`.

`SolvesDivisibleKUMBelow α r` records that all positive lower ranks are solved in this divisible sense.

The migrated theorem

`exists_cyclicBasisOrder_of_nonempty_proper_tight_of_lower_ranks`

proves:

> If divisible KUM is solved at every positive rank below `r`, then every finite uniformly dense rank-`r` matroid on `r*k` elements with a nonempty proper tight set has a cyclic basis ordering.

Thus, **inside the divisible subproblem**, new work at rank `r` can be restricted to instances having no nonempty proper tight set once all lower ranks are available.

## Low-rank bases

- Rank 1: **formalized internally** in `HigherRankKUM/LowRank/RankOne.lean`.
- Rank 2: **internalization pending**. A certified proof exists in the source project through HalfWeave, but HigherRankKUM intentionally has no live dependency on that code.
- Rank 3: **internalization pending**. The completed theorem exists in Rank3KUM, but HigherRankKUM intentionally has no live dependency on Rank3KUM.

Ranks 2 and 3 should eventually be supplied by native internal proofs or by a clearly marked immutable vendored snapshot with exact provenance. Until then, the generic induction theorem remains conditional on explicit solver certificates.

No axiom is introduced to bridge this gap.

## Rank 4

For the **divisible** rank-four subproblem (`|E| = 4k`), the generic theorem shows that all cases with a nonempty proper tight set reduce to ranks 1, 2, and 3. `HigherRankKUM/Rank4/TightReduction.lean` exposes this specialization while taking the missing rank-2 and rank-3 solver certificates explicitly.

Once ranks 2 and 3 are internalized, only the strictly uniformly dense divisible branch remains new within the divisible regime.

However, full rank-four KUM contains an additional arithmetic regime that did not occur in rank three: ground sizes with

`gcd(|E|, 4) = 2`, equivalently `|E| ≡ 2 (mod 4)`.

The present `SolvesDivisibleKUMAtRank` abstraction does **not** address that regime. Therefore the full rank-four research program must distinguish:

1. coprime cases (`gcd(|E|,4)=1`), handled by the existing coprime theorem in the literature;
2. divisible cases (`4 | |E|`), where the current tight-set induction machinery applies;
3. the intermediate gcd-two cases (`|E| ≡ 2 mod 4`), which require separate analysis unless covered by another theorem.

This arithmetic split should remain explicit in all rank-four planning documents.

## Rank 5 and rank 6 consequences already explored

The Rank3KUM higher-rank source branch contains formal corollaries showing, conditionally on lower-rank solvers:

- rank 5 divisible cases with a tight rank-2 or tight rank-3 set reduce to ranks 2+3 or 3+2;
- rank 6 divisible cases with a tight rank-3 set reduce to ranks 3+3.

These should be re-derived in HigherRankKUM from the generic reduction rather than copied with duplicated rank bookkeeping.

## Research frontier

Immediate targets are:

1. internalize certified rank 2 without introducing a live Rank3KUM dependency;
2. internalize certified rank 3 without introducing a live Rank3KUM dependency;
3. then discharge the explicit rank-2/rank-3 hypotheses in the divisible rank-four tight-set corollary;
4. characterize the strictly uniformly dense divisible rank-four branch;
5. separately investigate the `gcd(|E|,4)=2` regime;
6. determine which rank-three strict-branch ideas (deletion, repair, splicing, gap control) have meaningful rank-four analogues before porting any implementation.

See `docs/DEPENDENCY_POLICY.md` for the standalone-repository requirement.
