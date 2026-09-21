import HigherRankKUM.Rank4.BlockerDangerousBridge
import HigherRankKUM.Rank4.SaturatedFlatRankThree

namespace HigherRankKUM
namespace Rank4SaturatedBlockerExact

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- In the no-dangerous t=0 branch, a maximal blocker set has no hidden
closure elements.

If X has rank three, |X| = 3k-1, and a ground element e outside X lies in
cl(X), then no-dangerous geometry forces

  cl(X) = insert e X.

Thus the saturated rank-three flat has exactly 3k elements. -/
theorem closure_eq_insert_of_rankThree_saturated_blocker
    {M : Matroid α} {k : ℕ} {X : Set α} {e : α}
    (hk : 1 ≤ k)
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hXsub : X ⊆ M.E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hXcard : X.ncard = 3 * k - 1)
    (heE : e ∈ M.E)
    (heX : e ∉ X)
    (hecl : e ∈ M.closure X) :
    M.closure X = insert e X := by
  have hXfin : X.Finite := hGroundFin.subset hXsub
  have hclSub : M.closure X ⊆ M.E :=
    M.closure_subset_ground X
  have hclFin : (M.closure X).Finite :=
    hGroundFin.subset hclSub
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
      4 * (M.closure X).ncard < (4 * k + 2) * 3 := by
    exact_mod_cast hs
  have hclUpper : (M.closure X).ncard ≤ 3 * k + 1 := by
    omega

  have hnotTop : (M.closure X).ncard ≠ 3 * k + 1 := by
    intro hEq
    have hencard :
        (M.closure X).encard = ((3 * k + 1 : ℕ) : ℕ∞) := by
      rw [← hclFin.cast_ncard_eq, hEq]
    exact hNoDangerous (M.closure X)
      ⟨M.isFlat_closure X, hclRank, hencard⟩

  have hclLe : (M.closure X).ncard ≤ 3 * k := by
    omega

  have hinsSub : insert e X ⊆ M.closure X := by
    intro x hx
    rcases hx with rfl | hx
    · exact hecl
    · exact M.subset_closure X hXsub hx
  have hinsCard : (insert e X).ncard = 3 * k := by
    rw [Set.ncard_insert_of_notMem heX hXfin, hXcard]
    omega
  have hclLower : 3 * k ≤ (M.closure X).ncard := by
    have h :=
      Set.ncard_le_ncard hinsSub hclFin
    rw [hinsCard] at h
    exact h
  have hcardEq :
      (M.closure X).ncard = (insert e X).ncard := by
    rw [hinsCard]
    omega
  exact
    (Set.eq_of_subset_of_ncard_le
      hinsSub (by omega) hclFin).symm

/-- A maximal t=0 blocker flat is exactly X union {e}, has size 3k, and its
restriction is solved by the frozen rank-three KUM theorem. -/
theorem exists_rankThree_cbo_on_saturated_blocker_closure
    {M : Matroid α} {k : ℕ} {X : Set α} {e : α}
    (hk : 1 ≤ k)
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hXsub : X ⊆ M.E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hXcard : X.ncard = 3 * k - 1)
    (heE : e ∈ M.E)
    (heX : e ∉ X)
    (hecl : e ∈ M.closure X) :
    M.closure X = insert e X ∧
    ∃ order : Fin (3 * k) ≃ (M ↾ M.closure X).E,
      CyclicBasisOrder (M ↾ M.closure X) 3 (by omega) order := by
  have hEq :=
    closure_eq_insert_of_rankThree_saturated_blocker
      hk hGroundFin hRank hStrict hNoDangerous
      hXsub hXrank hXcard heE heX hecl
  have hclCard : (M.closure X).ncard = 3 * k := by
    rw [hEq, Set.ncard_insert_of_notMem heX
      (hGroundFin.subset hXsub), hXcard]
    omega
  have hclRank : M.eRk (M.closure X) = (3 : ℕ∞) := by
    rw [M.eRk_closure_eq, hXrank]
  refine ⟨hEq, ?_⟩
  exact
    Rank4SaturatedFlatRankThree.exists_cyclicBasisOrder_restrict_of_rankThree_ncard_three_mul
      (M := M) (H := M.closure X) hk hGroundFin hRank hStrict
      (M.closure_subset_ground X) hclRank hclCard

end

end Rank4SaturatedBlockerExact
end HigherRankKUM
