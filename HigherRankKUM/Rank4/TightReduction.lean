import HigherRankKUM.TightInduction
import HigherRankKUM.LowRank.RankOne
import HigherRankKUM.LowRank.RankTwo

namespace HigherRankKUM

noncomputable section

variable {α : Type*}

/--
Divisible rank-four KUM with a nonempty proper tight set reduces uniformly to
the divisible rank-one, rank-two, and rank-three solvers.

Ranks one and two are internal to HigherRankKUM. Rank three remains an explicit
solver certificate so the rank-four layer has no dependency on Rank3KUM.
-/
theorem exists_cyclicBasisOrder_of_rank_four_of_nonempty_proper_tight
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 4)
    (hEcard : M.E.encard = ((4 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E)
    (hSolve3 : SolvesDivisibleKUMAtRank α 3) :
    ∃ order : Fin (4 * k) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) order := by
  have hBelow : SolvesDivisibleKUMBelow α 4 := by
    intro s hs hslt
    have hs_cases : s = 1 ∨ s = 2 ∨ s = 3 := by
      omega
    rcases hs_cases with hs1 | hs23
    · subst s
      exact solvesDivisibleKUMAtRank_one
    · rcases hs23 with hs2 | hs3
      · subst s
        exact solvesDivisibleKUMAtRank_two
      · subst s
        exact hSolve3
  exact
    exists_cyclicBasisOrder_of_nonempty_proper_tight_of_lower_ranks
      M 4 k (by omega) hk hE hRank hEcard hDense
      hX hXnonempty hXproper hBelow

end

end HigherRankKUM
