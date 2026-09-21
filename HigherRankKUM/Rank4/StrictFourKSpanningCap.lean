import HigherRankKUM.StrictDensity

namespace HigherRankKUM
namespace Rank4StrictFourKSpanningCap

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- In a strict rank-four instance on 4k elements, a rank-three set that
spans a ground element outside itself has at most 3k-2 elements.

Strict density bounds the rank-three closure by 3k-1 elements.  Since the
closure contains at least one additional element beyond X, namely e, the
spanning set X loses one more slot. -/
theorem rankThree_spanning_ncard_le_three_mul_sub_two
    {M : Matroid α} {k : ℕ} {X : Set α} {e : α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k) 4)
    (hXsub : X ⊆ M.E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (heX : e ∉ X)
    (hecl : e ∈ M.closure X) :
    X.ncard ≤ 3 * k - 2 := by
  have hclSub : M.closure X ⊆ M.E :=
    M.closure_subset_ground X
  have hclFin : (M.closure X).Finite :=
    hE.subset hclSub
  have hclRank : M.eRk (M.closure X) = (3 : ℕ∞) := by
    rw [M.eRk_closure_eq, hXrank]
  have hclProper : M.closure X ≠ M.E := by
    intro hEq
    have hr := hclRank
    rw [hEq, M.eRk_ground, hRank] at hr
    norm_num at hr
  have hclNonempty : (M.closure X).Nonempty :=
    ⟨e, hecl⟩
  have hs :=
    hStrict (M.closure X) hclSub hclNonempty hclProper
  rw [← hclFin.cast_ncard_eq, hclRank] at hs
  have hsNat :
      4 * (M.closure X).ncard < (4 * k) * 3 := by
    exact_mod_cast hs
  have hclUpper : (M.closure X).ncard ≤ 3 * k - 1 := by
    omega
  have hne : X ≠ M.closure X := by
    intro hEq
    apply heX
    rw [hEq]
    exact hecl
  have hss : X ⊂ M.closure X :=
    (M.subset_closure X hXsub).ssubset_of_ne hne
  have hlt : X.ncard < (M.closure X).ncard :=
    Set.ncard_lt_ncard hss hclFin
  omega

end

end Rank4StrictFourKSpanningCap
end HigherRankKUM
