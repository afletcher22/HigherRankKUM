import HigherRankKUM.BalancedWindowDecomposition
import HigherRankKUM.BalancedGluing
import HigherRankKUM.Rank4.CyclicWindowFour
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4RankThreeFlatCore

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- A basis of a rank-three flat together with any ground element outside
that flat is an ambient rank-four basis. -/
theorem isBase_insert_outside_rankThree_flat
    {M : Matroid α} {H I : Set α} {c : α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hHflat : M.IsFlat H)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (hHfin : H.Finite)
    (hI : M.IsBasis I H)
    (hcE : c ∈ M.E)
    (hcH : c ∉ H) :
    M.IsBase (insert c I) := by
  have hcI : c ∉ I := by
    intro hcI
    exact hcH (hI.subset hcI)
  have hclH : M.closure H = H :=
    (Matroid.isFlat_iff_closure_eq).1 hHflat
  have hcCl : c ∉ M.closure I := by
    rw [hI.closure_eq_closure, hclH]
    exact hcH
  have hInd : M.Indep (insert c I) := by
    apply (hI.indep.insert_indep_iff_of_notMem hcI).2
    exact ⟨hcE, hcCl⟩
  have hIfin : I.Finite := hHfin.subset hI.subset
  have hInsFin : (insert c I).Finite := hIfin.insert c
  have hIcard : I.encard = (3 : ℕ∞) := by
    rw [hI.encard_eq_eRk, hHrank]
  have hInsCard : (insert c I).encard = (4 : ℕ∞) := by
    rw [Set.encard_insert_of_notMem hcI, hIcard]
    norm_num
  apply hInd.isBase_of_eRk_ge hInsFin
  rw [hRank, hInd.eRk_eq_encard, hInsCard]

/-- The cyclic one-window of an enumeration is its singleton current entry. -/
theorem cyclicWindow_one_eq_singleton
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow 1 hn σ i = {(σ i : α)} := by
  ext x
  simp only [cyclicWindow, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl⟩
    fin_cases q
    simp [cyclicIndex_zero]
  · intro hx
    subst x
    exact ⟨0, by simp [cyclicIndex_zero]⟩

/-- Balanced HHH-outside core construction.

Let H be a rank-three flat in a rank-four matroid.  Given a rank-three CBO
of H on 3k elements and any enumeration of k ground elements outside H,
interleaving them as repeated blocks H,H,H,C gives an ambient rank-four CBO
on the 4k-element subset H ∪ C.

No density hypothesis is used by this construction. -/
theorem exists_cyclicBasisOrder_rankThree_flat_plus_k_outside
    {M : Matroid α} {H C : Set α} {k : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = (4 : ℕ∞))
    (hHsub : H ⊆ M.E)
    (hHflat : M.IsFlat H)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (hHfin : H.Finite)
    (hCsub : C ⊆ M.E \ H)
    (σH : Fin (3 * k) ≃ (M.restrict H).E)
    (hHCBO : CyclicBasisOrder (M.restrict H) 3 (by omega) σH)
    (σC : Fin k ≃ C) :
    ∃ σ : Fin (4 * k) ≃ (H ∪ C : Set α),
      CyclicBasisOrder M 4 (by omega) σ := by
  let left : Fin (3 * k) ≃ H :=
    σH.trans (restrictGroundEquiv M H)
  let right : Fin (1 * k) ≃ C :=
    (finCongr (by omega : 1 * k = k)).trans σC
  have hDisjoint : Disjoint H C := by
    apply Set.disjoint_left.2
    intro x hxH hxC
    exact (hCsub hxC).2 hxH
  let raw : Fin ((3 + 1) * k) ≃ (H ∪ C : Set α) :=
    balancedBlockOrder hDisjoint left right
  let σ : Fin (4 * k) ≃ (H ∪ C : Set α) :=
    (finCongr (by omega : 4 * k = (3 + 1) * k)).trans raw
  refine ⟨σ, ?_⟩
  intro p
  let p' : Fin ((3 + 1) * k) :=
    (finCongr (by omega : 4 * k = (3 + 1) * k)) p
  obtain ⟨iH, iC, hdecomp⟩ :=
    cyclicWindow_balancedBlockOrder_decomposition
      (s := 3) (t := 1) (k := k)
      (by omega) (by omega) hk hDisjoint left right p'
  have hσwin :
      cyclicWindow 4 (by omega) σ p =
        cyclicWindow 1 (by omega) right iC ∪
          cyclicWindow 3 (by omega) left iH := by
    simpa [σ, raw, p', cyclicWindow] using hdecomp
  rw [hσwin]
  have hI :
      M.IsBasis (cyclicWindow 3 (by omega) left iH) H := by
    have hres := hHCBO iH
    have hres' :
        M.IsBasis (cyclicWindow 3 (by omega) σH iH) H :=
      (M.isBase_restrict_iff hHsub).1 hres
    simpa [left, cyclicWindow] using hres'
  have hOne :
      cyclicWindow 1 (by omega) right iC =
        {((right iC : C) : α)} :=
    cyclicWindow_one_eq_singleton (by omega) right iC
  rw [hOne, Set.singleton_union]
  apply isBase_insert_outside_rankThree_flat
    hRank hHflat hHrank hHfin hI
  · exact (hCsub (right iC).property).1
  · exact (hCsub (right iC).property).2

end

end Rank4RankThreeFlatCore
end HigherRankKUM
