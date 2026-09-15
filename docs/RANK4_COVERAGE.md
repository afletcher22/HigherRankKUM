# Rank-Four KUM Coverage Map

This document separates arithmetic regimes before structural case splitting. That distinction is essential in rank four.

## Arithmetic split

Let `n = |E(M)|` and `r(M)=4`.

### 1. Coprime regime

`gcd(n,4)=1`, equivalently `n` is odd.

This belongs to the existing coprime KUM theorem in the literature and is not the main target of the HigherRankKUM divisible machinery.

### 2. Intermediate gcd-two regime

`gcd(n,4)=2`, equivalently

`n ≡ 2 (mod 4)`.

This regime has no analogue in rank three: when `r=3`, every non-coprime size is automatically divisible by 3. At rank four, that implication fails.

The current HigherRankKUM abstraction `SolvesDivisibleKUMAtRank α 4` does not cover this regime because it assumes `n = 4k`.

### 3. Divisible regime

`4 | n`, so `n = 4k`.

This is the regime addressed by the migrated generic tight-set induction machinery.

## Structural split inside the divisible regime

Assume `n=4k` and uniform density with parameter `k`.

### Nonempty proper tight set

Once divisible KUM is supplied at ranks 1, 2, and 3, the arbitrary-rank theorem

`exists_cyclicBasisOrder_of_nonempty_proper_tight_of_lower_ranks`

immediately gives the rank-four result for every instance with a nonempty proper tight set.

Internally, a proper tight set can have rank 1, 2, or 3, so the factor splits are respectively:

- `1 + 3`;
- `2 + 2`;
- `3 + 1`.

The general theorem supersedes a hand-written case split as the production proof, while the old explicit Rank3KUM rank-four experiment remains useful as an independent regression oracle.

### No nonempty proper tight set

This is the strictly uniformly dense divisible rank-four branch. It is the main new structural target after the migration and low-rank adapters are complete.

The rank-three strict proof should be treated as a source of candidate proof patterns, not as code to port automatically. In particular, the following need fresh rank-four formulations:

- deletion preserving the relevant density margin;
- the replacement for the rank-three two-gap obstruction;
- repair/insertion conditions after solving a smaller instance;
- exchange-support or matching conditions controlling reinsertion;
- any finite exceptional geometry that replaces the rank-three six-point route.

## Current schematic coverage

```text
Rank-4 KUM
│
├── gcd(n,4)=1
│   └── coprime theorem in the literature
│
├── gcd(n,4)=2
│   └── separate higher-rank research branch (not covered by divisible machinery)
│
└── gcd(n,4)=4   [n=4k]
    │
    ├── nonempty proper tight set
    │   └── generic lower-rank tight-set induction
    │       ├── 1+3
    │       ├── 2+2
    │       └── 3+1
    │
    └── no nonempty proper tight set
        └── strict divisible rank-four research frontier
```

## Immediate formal milestone

After the rank-1/2/3 solver adapters are available, add a short theorem in `HigherRankKUM/Rank4/TightReduction.lean` deriving the entire nonempty-proper-tight divisible rank-four branch from the generic induction theorem. Do not reimplement the three factor cases there.
