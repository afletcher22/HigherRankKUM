import HigherRankKUM.Rank4.SaturatedSixDefectGluing
import HigherRankKUM.BalancedGluing
import HigherRankKUM.Rank4.CyclicWindowFour
import HigherRankKUM.Rank4.CyclicIndexArithmetic

namespace HigherRankKUM
namespace Rank4SaturatedSixDefectCertification

open Set
open scoped Matroid
open Rank4SaturatedSixDefectSchedule
open Rank4SaturatedSixDefectGluing

noncomputable section

variable {α : Type*}

/-- The explicit full-ground order obtained by feeding a rank-three CBO of H
and an enumeration of the complement into the six-defect schedule. -/
def saturatedFullOrder
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k)
    (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    Fin (4 * k + 2) ≃ M.E := by
  let left : Fin (3 * k) ≃ H :=
    flatOrder.trans (restrictGroundEquiv M H)
  let local : Fin (4 * k + 2) ≃
      (H ∪ (M.E \ H) : Set α) :=
    saturatedScheduleOrder hk Set.disjoint_sdiff_right left outsideOrder
  exact local.trans (Equiv.setCongr (Set.union_sdiff_cancel hHsub))

/-- The automatic basis theorem for an ordinary 3H+1R window, stated
directly with a cyclic rank-three window of the flat order. -/
theorem isBase_insert_outside_cyclicWindow_three
    {M : Matroid α} {H : Set α} {k : ℕ}
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hHsub : H ⊆ M.E)
    (hHflat : M.IsFlat H)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (hFlatCBO :
      CyclicBasisOrder (M ↾ H) 3 (by omega) flatOrder)
    (r : α)
    (hr : r ∈ M.E \ H)
    (i : Fin (3 * k)) :
    M.IsBase
      (insert r (cyclicWindow 3 (by omega) flatOrder i)) := by
  exact
    isBase_insert_outside_rankThree_flat
      hGroundFin hRank hHsub hHflat hHrank
      (hFlatCBO i) hr.1 hr.2

/-- Values of the full-ground schedule agree with the corresponding local
flat/complement slot value. -/
theorem saturatedFullOrder_value
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k)
    (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α))
    (i : Fin (4 * k + 2)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder i : α) =
      saturatedSlotValue
        (flatOrder.trans (restrictGroundEquiv M H))
        outsideOrder
        (saturatedIndexEquiv k hk i) := by
  rfl

end

end Rank4SaturatedSixDefectCertification
end HigherRankKUM
