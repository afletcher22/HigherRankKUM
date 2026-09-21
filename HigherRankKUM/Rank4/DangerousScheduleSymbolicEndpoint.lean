import HigherRankKUM.Rank4.DangerousBranchFactors
import HigherRankKUM.Rank4.DangerousHyperplaneGood
import HigherRankKUM.Rank4.DangerousScheduleNormalization
import HigherRankKUM.Rank4.DangerousScheduleSymbolicBasis
import HigherRankKUM.Rank4.DangerousScheduleSymbolicDistanceTwo

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- Unified active dangerous-hyperplane theorem.

For strict rank four on `4k+2` elements with `k ≥ 2`, the existence of a
single dangerous hyperplane implies a cyclic basis ordering, assuming the
rank-three KUM solver. The two good-edge configurations are normalized by
rotation and discharged by the symbolic adjacent/separated schedule proofs. -/
theorem exists_cbo_of_dangerous_hyperplane
    {M : Matroid α} {k : ℕ}
    (hSolve3 : SolvesKUMAtRank α 3)
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    {H : Set α}
    (hH : DangerousHyperplane M k H) :
    ∃ σ : Fin (4 * k + 2) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) σ := by
  obtain ⟨order, hOrder⟩ :=
    exists_hyperplane_cbo_of_one_dangerous
      hSolve3 hE hRank hStrict hH

  obtain ⟨i, hconfig⟩ :=
    dangerous_hyperplane_exists_good_edge_configuration
      hk hE hRank hEcard hStrict hH order hOrder

  rcases hconfig with hAdj | hTwo
  · obtain ⟨order', hOrder', hgoodEnd, hgoodWrap⟩ :=
      exists_shifted_adjacent_good_at_end
        hk order hOrder i hAdj.1 hAdj.2
    exact
      Rank4DangerousScheduleSymbolic.exists_cbo_of_adjacent_good_normalized_symbolic
        hk hE hRank hEcard hStrict hH
        order' hOrder' hgoodEnd hgoodWrap

  · obtain ⟨order', hOrder', hgood0, hgood2⟩ :=
      exists_shifted_distance_two_good_at_start
        hk order hOrder i hTwo.1 hTwo.2
    exact
      Rank4DangerousScheduleSymbolic.exists_cbo_of_distance_two_good_normalized_symbolic
        hk hE hRank hEcard hStrict hH
        order' hOrder' hgood0 hgood2

end

end Rank4DangerousBranches
end HigherRankKUM
