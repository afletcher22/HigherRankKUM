# Generalization Status

This file distinguishes certified generic infrastructure from rank-specific results and open research targets.

## Status vocabulary

- **Formalized generic** — Lean theorem has no fixed ambient-rank hypothesis and lives in the HigherRankKUM generic dependency chain.
- **Formalized conditional** — Lean theorem is generic but assumes lower-rank KUM solvers or other hypotheses not yet supplied internally by this repo.
- **Adapter pending** — theorem is already certified elsewhere and should be imported through a narrow interface rather than copied.
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

- Rank 1: generic proof exists in Rank3KUM and should be migrated directly.
- Rank 2: certified proof exists through the HalfWeave machinery; migration strategy still to be chosen.
- Rank 3: solved in Rank3KUM. HigherRankKUM should use a pinned adapter rather than copy the rank-three proof stack.

Until these are wired into HigherRankKUM, the generic induction theorem remains conditional.

## Rank 4

For the **divisible** rank-four subproblem (`|E| = 4k`), the generic theorem shows that all cases with a nonempty proper tight set reduce to ranks 1, 2, and 3. Once those base solvers are wired in, only the strictly uniformly dense divisible branch remains new.

However, full rank-four KUM contains an additional arithmetic regime that did not occur in rank three: ground sizes with

`gcd(|E|, 4) = 2`, equivalently `|E| ≡ 2 (mod 4)`.

The present `SolvesDivisibleKUMAtRank` abstraction does **not** address that regime. Therefore the full rank-four research program must distinguish:

1. coprime cases (`gcd(|E|,4)=1`), handled by the existing coprime theorem in the literature;
2. divisible cases (`4 | |E|`), where the current tight-set induction machinery applies;
3. the intermediate gcd-two cases (`|E| ≡ 2 mod 4`), which require separate analysis unless covered by another theorem.

This arithmetic split should remain explicit in all rank-four planning documents.

## Rank 5 and rank 6 consequences already explored

The Rank3KUM higher-rank branch contains formal corollaries showing, conditionally on the known lower-rank solvers:

- rank 5 divisible cases with a tight rank-2 or tight rank-3 set reduce to ranks 2+3 or 3+2;
- rank 6 divisible cases with a tight rank-3 set reduce to ranks 3+3.

These should be re-derived in HigherRankKUM from the generic reduction rather than copied with duplicated rank bookkeeping.

## Research frontier

Immediate mathematical targets after migration are:

1. wire certified ranks 1–3 into the abstract solver interface;
2. instantiate the generic theorem at divisible rank 4 and verify the old explicit rank-four reduction as a regression oracle;
3. characterize the strictly uniformly dense divisible rank-four branch;
4. separately investigate the `gcd(|E|,4)=2` regime;
5. determine which rank-three strict-branch ideas (deletion, repair, splicing, gap control) have meaningful rank-four analogues before porting any implementation.
