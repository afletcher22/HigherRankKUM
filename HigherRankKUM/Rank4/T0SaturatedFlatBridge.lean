import HigherRankKUM.Rank4.T0SaturatedCap
import HigherRankKUM.Rank4.SaturatedFlatRankThree

namespace HigherRankKUM
namespace Rank4T0SaturatedFlatBridge

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- A deletion-ground rank-three set saturating the t=0 cap is already the
entire deletion-ground part of its ambient closure.

With the original ground size 4k+2, the ambient closure is therefore exactly
X together with the omitted element e. -/
theorem closure_eq_insert_omitted_of_saturated
    {M : Matroid α} {k : ℕ} {E X : Set α} {e : α}
    (hk : 1 ≤ k)
    (hGroundFin : M.E.Finite)
    (hGroundCard : M.E.ncard = 4 * k + 2)
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
    (hXcard : X.ncard = 3 * k - 1)
    (sigma : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) sigma) :
    M.closure X = insert e X := by
  let Y : Set α := M.closure X ∩ E
  have hXground : X ⊆ M.E := hXsub.trans hEsub
  have hXY : X ⊆ Y := by
    intro x hx
    exact ⟨M.subset_closure X hXground hx, hXsub hx⟩
  have hYsub : Y ⊆ E := Set.inter_subset_right
  have hYfin : Y.Finite := hEfin.subset hYsub
  have hYrank : M.eRk Y = (3 : ℕ∞) := by
    apply le_antisymm
    · calc
        M.eRk Y ≤ M.eRk (M.closure X) :=
          M.eRk_mono Set.inter_subset_left
        _ = M.eRk X := M.eRk_closure_eq X
        _ = (3 : ℕ∞) := hXrank
    · calc
        (3 : ℕ∞) = M.eRk X := hXrank.symm
        _ ≤ M.eRk Y := M.eRk_mono hXY
  have heYcl : e ∈ M.closure Y := by
    exact M.closure_mono hXY hecl
  have hYcap :
      Y.ncard ≤ 3 * k - 1 :=
    Rank4T0SaturatedCap.rankThree_spanning_ncard_le_three_mul_sub_one_of_no_dangerous
      hGroundFin hRank hStrict hNoDangerous
      hEfin hEcard hEsub heE heNotE
      hYsub hYrank heYcl sigma hCBO
  have hXYeq : X = Y := by
    apply Set.eq_of_subset_of_ncard_le hXY
    · rw [hXcard]
      exact hYcap
    · exact hYfin
  have hclInter : M.closure X ∩ E = X := by
    simpa [Y] using hXYeq.symm

  have hInsertSub : insert e E ⊆ M.E := by
    intro x hx
    rcases hx with rfl | hxE
    · exact heE
    · exact hEsub hxE
  have hInsertCard : (insert e E).ncard = 4 * k + 2 := by
    rw [Set.ncard_insert_of_notMem heNotE, hEcard]
    omega
  have hGroundPartition : insert e E = M.E := by
    apply Set.eq_of_subset_of_ncard_le hInsertSub
    · rw [hGroundCard, hInsertCard]
    · exact hGroundFin

  apply Set.Subset.antisymm
  · intro x hxcl
    have hxGround : x ∈ M.E :=
      M.closure_subset_ground X hxcl
    rw [← hGroundPartition] at hxGround
    rcases hxGround with hxe | hxE
    · exact Or.inl hxe
    · have hxX : x ∈ X := by
        have hxInter : x ∈ M.closure X ∩ E := ⟨hxcl, hxE⟩
        rw [hclInter] at hxInter
        exact hxInter
      exact Or.inr hxX
  · intro x hx
    rcases hx with hxe | hxX
    · simpa [hxe] using hecl
    · exact M.subset_closure X hXground hxX

/-- A saturated deletion-ground blocker set therefore closes to a rank-three
3k-element flat, so the frozen Rank3KUM theorem supplies a CBO of that flat. -/
theorem exists_cyclicBasisOrder_saturated_closure
    {M : Matroid α} {k : ℕ} {E X : Set α} {e : α}
    (hk : 1 ≤ k)
    (hGroundFin : M.E.Finite)
    (hGroundCard : M.E.ncard = 4 * k + 2)
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
    (hXcard : X.ncard = 3 * k - 1)
    (sigma : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) sigma) :
    ∃ order : Fin (3 * k) ≃ (M ↾ M.closure X).E,
      CyclicBasisOrder (M ↾ M.closure X) 3 (by omega) order := by
  have hclEq :
      M.closure X = insert e X :=
    closure_eq_insert_omitted_of_saturated
      hk hGroundFin hGroundCard hRank hStrict hNoDangerous
      hEfin hEcard hEsub heE heNotE
      hXsub hXrank hecl hXcard sigma hCBO
  have heX : e ∉ X := by
    intro hex
    exact heNotE (hXsub hex)
  have hclCard : (M.closure X).ncard = 3 * k := by
    rw [hclEq, Set.ncard_insert_of_notMem heX, hXcard]
    omega
  have hclRank : M.eRk (M.closure X) = (3 : ℕ∞) := by
    rw [M.eRk_closure_eq, hXrank]
  have hclSub : M.closure X ⊆ M.E :=
    M.closure_subset_ground X
  exact
    Rank4SaturatedFlatRankThree.exists_cyclicBasisOrder_restrict_of_rankThree_ncard_three_mul
      hk hGroundFin hRank hStrict hclSub hclRank hclCard

end

end Rank4T0SaturatedFlatBridge
end HigherRankKUM
