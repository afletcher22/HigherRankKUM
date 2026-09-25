import HigherRankKUM.PrimeRank
import HigherRankKUM.Rank4.RationalTightReduction
import HigherRankKUM.Rank4.DangerousScheduleSymbolicEndpoint

/-!
# Rank-4 reductions without external hypotheses

Two rank-4 theorems took lower-rank KUM as an explicit hypothesis. Both are now discharged
internally:

* the `4k+2` case with a nonempty proper tight set needed rank-2 KUM at the odd size `2k+1`;
* the strict `4k+2` case with a dangerous hyperplane needed rank-3 KUM at every size.
-/

namespace HigherRankKUM

variable {α : Type*}

/-- Rank-4 KUM on `4k+2` elements with a nonempty proper tight set. -/
theorem exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight'
    (M : Matroid α) (k : ℕ) (hE : M.E.Finite) (hRank : M.eRank = 4)
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M (4 * k + 2) 4) {X : Set α}
    (hX : TightRatio M (4 * k + 2) 4 X) (hXnonempty : X.Nonempty) (hXproper : X ≠ M.E) :
    ∃ order : Fin (4 * k + 2) ≃ M.E, CyclicBasisOrder M 4 (by omega) order :=
  exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight M k hE hRank hEcard
    hDense hX hXnonempty hXproper (solvesKUMAtRankSize_two_odd k)

/-- Strict rank-4 KUM on `4k+2` elements with a dangerous hyperplane. -/
theorem Rank4DangerousBranches.exists_cbo_of_dangerous_hyperplane'
    {M : Matroid α} {k : ℕ} (hk : 2 ≤ k) (hE : M.E.Finite) (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4) {H : Set α}
    (hH : Rank4GcdTwoDeletion.DangerousHyperplane M k H) :
    ∃ σ : Fin (4 * k + 2) ≃ M.E, CyclicBasisOrder M 4 (by omega) σ :=
  Rank4DangerousBranches.exists_cbo_of_dangerous_hyperplane solvesKUMAtRank_three hk hE hRank
    hEcard hStrict hH

#print axioms solvesKUMAtRank_three
#print axioms exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight'
#print axioms Rank4DangerousBranches.exists_cbo_of_dangerous_hyperplane'

end HigherRankKUM
