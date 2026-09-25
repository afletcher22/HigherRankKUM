# Rank-4 KUM: formalization status

This page tracks what is proved in Lean for the rank-4 proof of `RANK4_EXTENSION_THEOREM.md` §5,
and what remains. Every theorem listed as proved depends only on
`[propext, Classical.choice, Quot.sound]`, the Palomar axiom set.

Last updated: 2026-09-25.

## Proved

| Result | Lean name | Where |
|---|---|---|
| vHT Theorem 2.1 | `HigherRankKUM.VHT.theorem_2_1` | main library, `HigherRankKUM/VHT/` |
| Coprime KUM, every rank (vHT 3.1) | `HigherRankKUM.VHT.solvesKUMAtRankSize_of_coprime` | main library |
| Edmonds partition, double covers | `VHT.edmonds_partition`, `VHT.double_cover` (given `theorem_2_1`) | main library |
| Prime rank: divisible KUM ⇒ full KUM | `HigherRankKUM.solvesKUMAtRank_of_prime` | main library, `PrimeRank.lean` |
| Full rank-3 KUM | `HigherRankKUM.solvesKUMAtRank_three` | main library |
| Rank-2 KUM, odd sizes | `HigherRankKUM.solvesKUMAtRankSize_two_odd` | main library |
| Rank 4, `4k+2`, proper tight set | `exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight'` | main library, `Rank4/Unconditional.lean` |
| Rank 4, strict `4k+2`, dangerous hyperplane (t>0) | `Rank4DangerousBranches.exists_cbo_of_dangerous_hyperplane'` | main library |
| Rank 4 on 4k elements with a nonempty proper tight set | `exists_cyclicBasisOrder_of_rank_four_of_nonempty_proper_tight` | main library (older) |
| KUM(4,6), from its certificate | `Probe.Enc.Kum6.solves` | `probe/encoding` |
| KUM(4,8), from its certificate | `Probe.Enc.Kum8.solves` | `probe/rank4` |
| **Theorem D, given X′** | `solvesDivisibleKUMAtRank_four_of_extension` | `probe/rank4` |

Theorem D in full takes `(∀ N ≥ 8, Rank4Extension α N)` and returns `SolvesDivisibleKUMAtRank α 4`.
`Rank4Extension α N` is the extension theorem X′ stated for `N` elements. The 8-element base case
is discharged by the certificate.

## Remaining for full rank-4 KUM

1. **X′ (`Rank4Extension α N`)**:
   * `N = 8, 12` (Theorem D) and `N = 10` (Theorem T): the cyclic certificates `cyc8`, `cyc12`,
     `cyc10`. Each fits the kernel budget: 237k–445k LRAT hints.
   * `N ≥ 14`: the local lemma X (`lin14`, 358k hints), plus a Lean argument. Interleave `S`
     into 14 consecutive entries; every window that touches `S` stays inside that stretch.
   * This needs a second witness family (basis unit clauses and interleaving clauses) and a
     bridge from a working interleaving to a cyclic ordering.
2. **Theorem T** (strict t=0, `n = 4k+2`):
   * Lemma U (paper; hypothesis: a double cover, which `VHT.double_cover` supplies) for `k ≥ 4`;
   * Lemma H (paper);
   * the `k = 3` cases through Theorems G and L4 (decision of 2026-09-25). Their SAT base lemmas
     are measured: the L4 base lemma is at the ceiling, with 826k hints, and needs a case split.
3. **Small cases**:
   * n = 6 is done;
   * n = 10: the strict t=0 part only (`kum10s`), since tight and t>0 are covered in Lean. Its
     LRAT size is still pending; the full n=10 formula is too large;
   * odd `n` is done, by coprime KUM.
4. **Assembly**: combine all branches into `SolvesKUMAtRank α 4`.
5. **Packaging**:
   * move the probe modules (`Enc*`, `Rank4/TheoremD*`) into the main library, with the heavy
     certificate modules in a separate library that is not built by default;
   * write the Palomar challenge statement and `formalization.yaml`.
