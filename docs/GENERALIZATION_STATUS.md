# Generalization Status

This file distinguishes certified generic infrastructure from rank-specific results and open research targets.

## Status vocabulary

- **Formalized generic** — Lean theorem has no fixed ambient-rank hypothesis and lives in the HigherRankKUM generic dependency chain.
- **Formalized internal** — the required rank-specific result is available inside this repository and builds without an external Rank3KUM dependency.
- **Research target** — no formal proof is currently present in HigherRankKUM.

## Formalized generic infrastructure

HigherRankKUM contains arbitrary-rank formalizations of:

- `UniformlyDense` and `Tight`;
- uniform-density inheritance under restriction;
- tight sets as flats in finite uniformly dense matroids;
- looplessness from positive uniform density;
- `cyclicIndex`, `cyclicWindow`, and arbitrary-rank `CyclicBasisOrder`;
- contraction rank bookkeeping and basis lifting;
- uniform-density inheritance under contraction by a finite tight set;
- abstract restriction/contraction window gluing;
- balanced `(L^s R^t)^k` interleaving and cyclic-window decomposition;
- concrete arbitrary-rank balanced restriction/contraction gluing;
- `SolvesDivisibleKUMAtRank` and `SolvesDivisibleKUMBelow`;
- generic tight-factor reduction;
- `exists_cyclicBasisOrder_of_nonempty_proper_tight_of_lower_ranks`.

The last theorem proves that, inside the divisible subproblem, any finite uniformly dense rank-`r` instance on `r*k` elements with a nonempty proper tight set reduces to solved positive ranks below `r`.

## Low-rank bases

- Rank 1: **formalized internally** in `HigherRankKUM/LowRank/RankOne.lean`.
- Rank 2: **formalized internally** in `HigherRankKUM/LowRank/RankTwo.lean` and its focused support modules.
- Rank 3: **formalized internally through a frozen vendored proof**. `vendor/Rank3KUM/` is an exact source snapshot of Rank3KUM version-3 commit `eff642a2e01fac4fc1f6f76e592eeea46c3152c9`; `HigherRankKUM/LowRank/RankThree.lean` translates `Rank3KUM.rankThreeKUM` into the generic solver interface.

Accordingly, HigherRankKUM now provides:

- `solvesDivisibleKUMAtRank_one`;
- `solvesDivisibleKUMAtRank_two`;
- `solvesDivisibleKUMAtRank_three`.

No axiom or live external Rank3KUM dependency is used.

## Rank 4

For the **divisible** rank-four subproblem (`|E| = 4k`), all positive lower ranks are now internally available. Therefore

`exists_cyclicBasisOrder_of_rank_four_of_nonempty_proper_tight`

is an unconditional internal theorem (subject only to its mathematical hypotheses): every finite uniformly dense rank-four matroid on `4k` elements having a nonempty proper tight set admits a cyclic basis ordering.

Thus the remaining new structural target inside the divisible regime is the case with **no nonempty proper tight set**, i.e. the strictly uniformly dense rank-four branch.

Full rank-four KUM additionally has the arithmetic regime

`gcd(|E|,4)=2`, equivalently `|E| ≡ 2 (mod 4)`.

The present divisible interface does not address that regime. Full rank-four planning therefore remains split into:

1. coprime cases (`gcd(|E|,4)=1`), handled by the existing coprime theorem in the literature;
2. divisible cases (`4 | |E|`), with the proper-tight branch now formally discharged and the strict branch open;
3. intermediate gcd-two cases (`|E| ≡ 2 mod 4`), requiring separate analysis unless covered by another result.

## Rank 5 and rank 6

Earlier Rank3KUM higher-rank experiments established conditional consequences such as rank-5 tight ranks `2/3` and rank-6 tight rank `3`. These should be re-derived here from the generic theorem when useful rather than copied with duplicate bookkeeping.

## Research frontier

The immediate new mathematical fronts are now:

1. characterize the strictly uniformly dense divisible rank-four branch;
2. audit the literature for the rank-four `gcd=2` regime and formulate the correct arithmetic reduction if none already covers it;
3. determine which rank-three strict-branch ideas—deletion, repair, splicing, gap control, exchange support—have genuine rank-four analogues;
4. use the solved proper-tight branch as a structural filter in computational rank-four searches.

See `docs/DEPENDENCY_POLICY.md` and `docs/RANK4_COVERAGE.md`.
