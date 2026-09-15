# Rank-Four KUM Coverage Map

This document separates arithmetic regimes before structural case splitting. That distinction is essential in rank four.

Let `n = |E(M)|` and `r(M)=4`.

## Arithmetic split

### 1. Coprime regime

`gcd(n,4)=1`, equivalently `n` is odd.

This belongs to the existing coprime KUM theorem in the literature and is not the main target of the HigherRankKUM divisible machinery.

### 2. Intermediate gcd-two regime

`gcd(n,4)=2`, equivalently `n ≡ 2 (mod 4)`.

This regime has no analogue in rank three: for rank 3, every non-coprime size is divisible by 3. The current `SolvesDivisibleKUMAtRank α 4` abstraction does not cover this regime because it assumes `n=4k`.

### 3. Divisible regime

`4 | n`, so `n=4k`.

This is the regime addressed by the generic tight-set induction machinery.

## Structural split inside the divisible regime

Assume `n=4k` and uniform density with parameter `k`.

### Nonempty proper tight set — formalized

Ranks 1, 2, and 3 are all available internally in HigherRankKUM. Therefore the arbitrary-rank theorem

`exists_cyclicBasisOrder_of_nonempty_proper_tight_of_lower_ranks`

specializes to the unconditional internal theorem

`exists_cyclicBasisOrder_of_rank_four_of_nonempty_proper_tight`.

Thus every finite uniformly dense rank-four matroid on `4k` elements with a nonempty proper tight set has a cyclic basis ordering.

A proper tight set has rank 1, 2, or 3, corresponding conceptually to:

- `1 + 3`;
- `2 + 2`;
- `3 + 1`.

The production proof does not hand-split these cases; the generic lower-rank induction theorem handles them uniformly. Rank 3 is supplied by the frozen local v3 proof under `vendor/Rank3KUM/`.

### No nonempty proper tight set — open structural frontier

This is the strictly uniformly dense divisible rank-four branch. It is now the only new structural branch remaining **inside the divisible regime**.

The rank-three strict proof is a source of proof patterns, not code to port mechanically. Fresh rank-four formulations are needed for:

- deletion preserving an adequate density margin;
- the replacement for the rank-three two-gap obstruction;
- repair/insertion after solving a smaller instance;
- exchange-support or matching conditions controlling reinsertion;
- finite exceptional geometry, if any, replacing the rank-three six-point route.

## Current schematic coverage

```text
Rank-4 KUM
│
├── gcd(n,4)=1
│   └── coprime theorem in the literature
│
├── gcd(n,4)=2
│   └── separate arithmetic research branch
│
└── gcd(n,4)=4   [n=4k]
    │
    ├── nonempty proper tight set
    │   └── SOLVED / FORMALIZED in HigherRankKUM
    │       ├── 1+3
    │       ├── 2+2
    │       └── 3+1
    │
    └── no nonempty proper tight set
        └── OPEN: strict divisible rank-four frontier
```

## Immediate research milestones

1. Audit the literature specifically for `gcd(n,4)=2` results before inventing new arithmetic machinery.
2. Characterize the strict divisible rank-four class computationally and structurally.
3. Test deletion/reinsertion and exchange-support formulations on finite rank-four examples.
4. Keep the strict-divisible and gcd-two tracks separate until a theorem genuinely connects them.

See `docs/GENERALIZATION_STATUS.md` and `experiments/rank4/README.md`.
