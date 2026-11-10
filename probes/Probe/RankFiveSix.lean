import HigherRankKUM.Skeleton
import HigherRankKUM.VHT.BlockChain
import Probe.Corank

/-!
# The skeleton at ranks 5 and 6

With full KUM at ranks 1 to 4, the rank-`r` skeleton (`HigherRankKUM/Skeleton.lean`) gives:

* **rank 5**: KUM follows from its strict case at the sizes `n = 5k`, `k ≥ 2`
  (`solvesKUMAtRank_five_of_strict`);
* **rank 6**, `gcd(n, 6) = 2` or `3`: a uniformly dense matroid with a nonempty proper tight set
  has a cyclic basis ordering (`exists_cyclicBasisOrder_of_rank_six_of_nonempty_proper_tight`).
  Its tight sets have rank `3`, or `2` and `4`, so only the solved ranks are needed.
-/

namespace HigherRankKUM

variable {α : Type*}

/-- Full KUM at every rank below 5. -/
theorem solvesKUMBelow_five : SolvesKUMBelow α 5 := by
  intro s hs hlt
  have h : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by omega
  rcases h with h | h | h | h
  · rw [h]
    exact solvesKUMAtRank_one
  · rw [h]
    exact solvesKUMAtRank_two
  · rw [h]
    exact solvesKUMAtRank_three
  · rw [h]
    exact solvesKUMAtRank_four

/-- **Rank 5 reduces to its strict divisible case**: the sizes `n ≥ 10` not coprime to 5. -/
theorem solvesKUMAtRank_five_of_strict
    (hStrict : ∀ n, 10 ≤ n → ¬ Nat.Coprime 5 n → SolvesStrictKUMAtRankSize α 5 n) :
    SolvesKUMAtRank α 5 :=
  solvesKUMAtRank_of_strict_large solvesKUMBelow_five
    (fun n hn hcop => hStrict n (by omega) hcop)

/-- **Rank 6 with a tight set**, for `gcd(n, 6) = 2` or `3`: a uniformly dense rank-6 matroid on
`n` elements with a nonempty proper tight set has a cyclic basis ordering. -/
theorem exists_cyclicBasisOrder_of_rank_six_of_nonempty_proper_tight
    (M : Matroid α) {n : ℕ} (hn : 0 < n)
    (hgcd : Nat.gcd n 6 = 2 ∨ Nat.gcd n 6 = 3)
    (hE : M.E.Finite)
    (hRank : M.eRank = ((6 : ℕ) : ℕ∞))
    (hEcard : M.E.encard = (n : ℕ∞))
    (hDense : UniformlyDenseRatio M n 6)
    {X : Set α}
    (hX : TightRatio M n 6 X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    ∃ order : Fin n ≃ M.E, CyclicBasisOrder M 6 hn order := by
  refine exists_cyclicBasisOrder_of_nonempty_proper_tight_of_multiples M (by norm_num) hn hE
    hRank hEcard hDense hX hXnonempty hXproper ?_
  intro s hs0 hs6 hdvd
  rcases hgcd with h | h
  · have hdvd' : 3 ∣ s := by simpa [h] using hdvd
    have hs : s = 3 := by omega
    rw [hs]
    exact solvesKUMAtRank_three
  · have hdvd' : 2 ∣ s := by simpa [h] using hdvd
    have hs : s = 2 ∨ s = 4 := by omega
    rcases hs with hs | hs
    · rw [hs]
      exact solvesKUMAtRank_two
    · rw [hs]
      exact solvesKUMAtRank_four

#print axioms solvesKUMAtRank_of_strict_large
#print axioms solvesKUMAtRank_five_of_strict
#print axioms exists_cyclicBasisOrder_of_rank_six_of_nonempty_proper_tight

end HigherRankKUM
