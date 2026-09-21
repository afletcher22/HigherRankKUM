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


/-- The six exceptional starts of the fixed saturated-flat schedule. -/
def saturatedDefectStarts (k : ℕ) (hk : 2 ≤ k) :
    Set (Fin (4 * k + 2)) :=
  let p := 4 * (k - 2)
  ({⟨p + 2, by omega⟩,
    ⟨p + 3, by omega⟩,
    ⟨p + 5, by omega⟩,
    ⟨p + 6, by omega⟩,
    ⟨p + 7, by omega⟩,
    ⟨p + 8, by omega⟩} : Set (Fin (4 * k + 2)))

/-- Abstract six-defect certification theorem.

Once every nonexceptional rank-four window is identified as one outside
element plus a cyclic rank-three basis window of H, the only remaining
matroid obligations are the six explicitly named defect windows. -/
theorem cyclicBasisOrder_of_saturated_six_defect_decomposition
    {M : Matroid α} {H : Set α} {k : ℕ}
    (hk : 2 ≤ k)
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hHsub : H ⊆ M.E)
    (hHflat : M.IsFlat H)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α))
    (fullOrder : Fin (4 * k + 2) ≃ M.E)
    (hFlatCBO :
      CyclicBasisOrder (M ↾ H) 3 (by omega) flatOrder)
    (hAuto :
      ∀ i : Fin (4 * k + 2),
        i ∉ saturatedDefectStarts k hk →
        ∃ iH : Fin (3 * k), ∃ iR : Fin (k + 2),
          cyclicWindow 4 (by omega) fullOrder i =
            insert (outsideOrder iR : α)
              (cyclicWindow 3 (by omega) flatOrder iH))
    (h2 :
      M.IsBase (cyclicWindow 4 (by omega) fullOrder
        ⟨4 * (k - 2) + 2, by omega⟩))
    (h3 :
      M.IsBase (cyclicWindow 4 (by omega) fullOrder
        ⟨4 * (k - 2) + 3, by omega⟩))
    (h5 :
      M.IsBase (cyclicWindow 4 (by omega) fullOrder
        ⟨4 * (k - 2) + 5, by omega⟩))
    (h6 :
      M.IsBase (cyclicWindow 4 (by omega) fullOrder
        ⟨4 * (k - 2) + 6, by omega⟩))
    (h7 :
      M.IsBase (cyclicWindow 4 (by omega) fullOrder
        ⟨4 * (k - 2) + 7, by omega⟩))
    (h8 :
      M.IsBase (cyclicWindow 4 (by omega) fullOrder
        ⟨4 * (k - 2) + 8, by omega⟩)) :
    CyclicBasisOrder M 4 (by omega) fullOrder := by
  intro i
  by_cases hi : i ∈ saturatedDefectStarts k hk
  · simp only [saturatedDefectStarts, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi
    rcases hi with hi | hi | hi | hi | hi | hi
    · simpa [hi] using h2
    · simpa [hi] using h3
    · simpa [hi] using h5
    · simpa [hi] using h6
    · simpa [hi] using h7
    · simpa [hi] using h8
  · obtain ⟨iH, iR, hwin⟩ := hAuto i hi
    rw [hwin]
    exact
      isBase_insert_outside_cyclicWindow_three
        hGroundFin hRank hHsub hHflat hHrank
        flatOrder hFlatCBO
        (outsideOrder iR : α) (outsideOrder iR).property iH

end

end Rank4SaturatedSixDefectCertification
end HigherRankKUM
