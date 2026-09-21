import HigherRankKUM.Rank4.BlockerDangerousBridge
import HigherRankKUM.Rank4.CyclicFlatCapacity

namespace HigherRankKUM
namespace Rank4T0SaturatedCap

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- In the no-dangerous `4k+2` branch, a rank-three set in a `4k+1`
deletion CBO that spans the omitted element has at most `3k-1` elements.

The ordinary cyclic-basis packing bound gives `|X| ≤ 3k`.  Equality would
make `X` a saturated rank-three blocker set, and the
blocker-dangerous bridge would then force `cl(X)` to be a dangerous
hyperplane. -/
theorem rankThree_spanning_ncard_le_three_mul_sub_one_of_no_dangerous
    {M : Matroid α} {k : ℕ} {E X : Set α} {e : α}
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hEfin : E.Finite)
    (hEcard : E.ncard = 4 * k + 1)
    (hEsub : E ⊆ M.E)
    (heE : e ∈ M.E)
    (heNotE : e ∉ E)
    (hXsub : X ⊆ E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hecl : e ∈ M.closure X)
    (σ : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    X.ncard ≤ 3 * k - 1 := by
  have hcap : X.ncard ≤ 3 * k :=
    Rank4CyclicFlatCapacity.rankThree_ncard_le_three_mul_of_cyclicBasisOrder
      hEfin hEcard hXsub hRank hXrank.le σ hCBO
  by_contra hnot
  have hEq : X.ncard = 3 * k := by
    omega
  have hXground : X ⊆ M.E :=
    hXsub.trans hEsub
  have heX : e ∉ X := by
    intro hex
    exact heNotE (hXsub hex)
  exact
    (Rank4BlockerDangerousBridge.not_mem_closure_rankThree_saturated_of_no_dangerous
      hGroundFin hRank hStrict hNoDangerous
      hXground hXrank hEq heE heX) hecl

end

end Rank4T0SaturatedCap
end HigherRankKUM
