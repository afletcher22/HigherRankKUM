import HigherRankKUM.Rank4.SaturatedSixDefectSchedule
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Rank.ENat

namespace HigherRankKUM
namespace Rank4SaturatedSixDefectGluing

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- A basis of a rank-three flat, together with any ground element outside the
flat, is a basis of a rank-four matroid.

This is the automatic 3H+1R window lemma for saturated-flat gluing. -/
theorem isBase_insert_outside_rankThree_flat
    {M : Matroid α} {H B : Set α} {r : α}
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hHsub : H ⊆ M.E)
    (hHflat : M.IsFlat H)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (hB : (M ↾ H).IsBase B)
    (hrE : r ∈ M.E)
    (hrH : r ∉ H) :
    M.IsBase (insert r B) := by
  have hBasis : M.IsBasis B H :=
    (Matroid.isBase_restrict_iff hHsub).mp hB
  have hrB : r ∉ B := by
    intro hrB
    exact hrH (hBasis.subset hrB)
  have hclH : M.closure H = H :=
    (Matroid.isFlat_iff_closure_eq).mp hHflat
  have hclB : M.closure B = H :=
    hBasis.closure_eq_closure.trans hclH
  have hrcl : r ∉ M.closure B := by
    rw [hclB]
    exact hrH
  have hinsInd : M.Indep (insert r B) := by
    rw [hBasis.indep.insert_indep_iff_of_notMem hrB]
    exact ⟨hrE, hrcl⟩
  have hinsSub : insert r B ⊆ M.E := by
    rw [insert_subset_iff]
    exact ⟨hrE, hBasis.indep.subset_ground⟩
  have hinsFin : (insert r B).Finite :=
    hGroundFin.subset hinsSub
  apply hinsInd.isBase_of_eRk_ge hinsFin
  have hInsRank :=
    M.eRk_insert_eq_add_one (X := B) ⟨hrE, hrcl⟩
  rw [hInsRank, hBasis.eRk_eq_eRk, hHrank, hRank]
  norm_num

end

end Rank4SaturatedSixDefectGluing
end HigherRankKUM
