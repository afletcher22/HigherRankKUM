import HigherRankKUM.Rank4.BlockerDangerousBridge

namespace HigherRankKUM
namespace Rank4T0SaturatedExactClosure

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- In the no-dangerous t=0 branch, a rank-three set of deletion size
`3k-1` that spans the omitted element has no hidden extra points in its
closure.

Its closure is exactly `X ∪ {e}` and therefore has `3k` elements.  Strict
density permits at most `3k+1` points in a rank-three flat; the latter value
would be a dangerous hyperplane, while `insert e X` already supplies
`3k` points. -/
theorem closure_eq_insert_of_rankThree_saturated_minus_one
    {M : Matroid α} {k : ℕ} {X : Set α} {e : α}
    (hk : 0 < k)
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
      (M.closure X).ncard = 3 * k := by
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
  have hupper : (M.closure X).ncard ≤ 3 * k + 1 := by
    omega
  have hInsertSub : insert e X ⊆ M.closure X := by
    intro x hx
    rcases hx with rfl | hx
    · exact hecl
    · exact M.subset_closure X hXsub hx
  have hInsertCard : (insert e X).ncard = 3 * k := by
    rw [Set.ncard_insert_of_notMem heX hXfin, hXcard]
    omega
  have hlower : 3 * k ≤ (M.closure X).ncard := by
    rw [← hInsertCard]
    exact Set.ncard_le_ncard hInsertSub hclFin
  have hnotTop : (M.closure X).ncard ≠ 3 * k + 1 := by
    intro hcard
    apply hNoDangerous (M.closure X)
    refine ⟨M.isFlat_closure X, hclRank, ?_⟩
    rw [← hclFin.cast_ncard_eq, hcard]
  have hclCard : (M.closure X).ncard = 3 * k := by
    omega
  have hEqInsert : insert e X = M.closure X := by
    apply Set.eq_of_subset_of_ncard_le hInsertSub
    rw [hclCard, hInsertCard]
  exact ⟨hEqInsert.symm, hclCard⟩

/-- The saturated flat has exactly `k+2` ambient points outside it. -/
theorem closure_complement_ncard_eq_k_add_two
    {M : Matroid α} {k : ℕ} {X : Set α} {e : α}
    (hk : 0 < k)
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.ncard = 4 * k + 2)
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hXsub : X ⊆ M.E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hXcard : X.ncard = 3 * k - 1)
    (heE : e ∈ M.E)
    (heX : e ∉ X)
    (hecl : e ∈ M.closure X) :
    (M.E \ M.closure X).ncard = k + 2 := by
  have hclCard :
      (M.closure X).ncard = 3 * k :=
    (closure_eq_insert_of_rankThree_saturated_minus_one
      hk hGroundFin hRank hStrict hNoDangerous
      hXsub hXrank hXcard heE heX hecl).2
  rw [Set.ncard_sdiff' (M.closure_subset_ground X) hGroundFin,
    hEcard, hclCard]
  omega

end

end Rank4T0SaturatedExactClosure
end HigherRankKUM
