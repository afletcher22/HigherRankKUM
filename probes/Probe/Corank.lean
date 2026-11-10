import HigherRankKUM.Duality
import HigherRankKUM.PrimeRank
import HigherRankKUM.LowRank.RankOne
import HigherRankKUM.LowRank.RankTwo
import Probe.Rank4.Final

/-!
# KUM for corank at most 4

Full KUM holds at ranks 1, 2, 3 and 4. By duality (`SolvesKUMAtRankSize.of_dual`), KUM at rank
`r` and size `n` follows from KUM at rank `n - r` and size `n`. So every finite uniformly dense
matroid of rank `r` on `n ≤ r + 4` elements has a cyclic basis ordering, for every `r`.

The rank-3 input is the vendored theorem with coprime KUM (`solvesKUMAtRank_three`); the rank-4
input is `solvesKUMAtRank_four`.
-/

namespace HigherRankKUM

variable {α : Type*}

/-- **Rank-1 KUM**, at every ground-set size. -/
theorem solvesKUMAtRank_one : SolvesKUMAtRank α 1 := by
  intro n N _hr hn hE hRank hEcard hDense
  have hDense' : UniformlyDense N n := (uniformlyDenseRatio_one_iff N n).1 hDense
  have hRank' : N.eRank = 1 := by simpa using hRank
  exact exists_cyclicBasisOrder_congr N (Nat.one_mul n) rfl
    (exists_cyclicBasisOrder_of_rank_one N n hn hE hRank' hEcard hDense')

/-- **Rank-2 KUM**, at every ground-set size: the divisible theorem and coprime KUM. -/
theorem solvesKUMAtRank_two : SolvesKUMAtRank α 2 :=
  solvesKUMAtRank_of_prime Nat.prime_two solvesDivisibleKUMAtRank_two

/-- **KUM for corank at most 4**: a finite uniformly dense matroid of rank `r` on `n ≤ r + 4`
elements has a cyclic basis ordering. -/
theorem solvesKUMAtRankSize_of_corank_le_four {r n : ℕ} (h : n ≤ r + 4) :
    SolvesKUMAtRankSize α r n := by
  rcases Nat.lt_trichotomy n r with hlt | heq | hgt
  · -- `n < r` is impossible: the rank is at most the size
    intro N _hr _hn _hE hRank hEcard _hDense
    exfalso
    have hle := N.eRk_le_encard N.E
    rw [N.eRk_ground, hRank, hEcard] at hle
    have hle' : r ≤ n := by exact_mod_cast hle
    omega
  · rw [heq]
    exact solvesKUMAtRankSize_self r
  · apply SolvesKUMAtRankSize.of_dual hgt
    have hc : n - r = 1 ∨ n - r = 2 ∨ n - r = 3 ∨ n - r = 4 := by omega
    rcases hc with hc | hc | hc | hc
    · rw [hc]
      exact solvesKUMAtRank_one n
    · rw [hc]
      exact solvesKUMAtRank_two n
    · rw [hc]
      exact solvesKUMAtRank_three n
    · rw [hc]
      exact solvesKUMAtRank_four n

#print axioms solvesKUMAtRankSize_dual_iff
#print axioms solvesKUMAtRankSize_of_corank_le_four

end HigherRankKUM
