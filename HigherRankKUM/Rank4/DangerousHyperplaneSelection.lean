import HigherRankKUM.Rank4.DangerousHyperplaneGood
import HigherRankKUM.RankTwoSelection
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- Two adjacent good core edges admit a common complementary pair that
certifies both exceptional ambient windows. -/
theorem dangerous_hyperplane_adjacent_good_selection
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (i : Fin (3 * k + 1))
    (hgood0 : DangerousHyperplaneEdgeGood order i)
    (hgood1 :
      DangerousHyperplaneEdgeGood order
        (cyclicIndex (3 * k + 1) (by omega) i 1)) :
    ∃ c₀ c₁ : α,
      c₀ ≠ c₁ ∧
      c₀ ∈ M.E \ H ∧ c₁ ∈ M.E \ H ∧
      let P₀ : Set α :=
        {(order i : α),
          (order (cyclicIndex (3 * k + 1) (by omega) i 1) : α)}
      let i₁ := cyclicIndex (3 * k + 1) (by omega) i 1
      let P₁ : Set α :=
        {(order i₁ : α),
          (order (cyclicIndex (3 * k + 1) (by omega) i₁ 1) : α)}
      M.IsBase (({c₀, c₁} : Set α) ∪ P₀) ∧
      M.IsBase (({c₀, c₁} : Set α) ∪ P₁) := by
  let hn : 0 < 3 * k + 1 := by omega
  let C : Set α := M.E \ H
  let i₁ : Fin (3 * k + 1) := cyclicIndex (3 * k + 1) hn i 1
  let P₀ : Set α := {(order i : α), (order i₁ : α)}
  let P₁ : Set α :=
    {(order i₁ : α),
      (order (cyclicIndex (3 * k + 1) hn i₁ 1) : α)}
  let N₀ : Matroid α := (M.contract P₀).restrict C
  let N₁ : Matroid α := (M.contract P₁).restrict C

  have hPair₀ :=
    dangerous_hyperplane_core_pair_indep_rank_two
      (by omega : 1 ≤ k) hH order hOrder i
  have hP₀ind : M.Indep P₀ := by
    simpa [P₀, i₁, hn] using hPair₀.1
  have hP₀rank : M.eRk P₀ = (2 : ℕ∞) := by
    simpa [P₀, i₁, hn] using hPair₀.2

  have hPair₁ :=
    dangerous_hyperplane_core_pair_indep_rank_two
      (by omega : 1 ≤ k) hH order hOrder i₁
  have hP₁ind : M.Indep P₁ := by
    simpa [P₁, i₁, hn] using hPair₁.1
  have hP₁rank : M.eRk P₁ = (2 : ℕ∞) := by
    simpa [P₁, i₁, hn] using hPair₁.2

  have hP₀sub : P₀ ⊆ H := by
    intro x hx
    simp only [P₀, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa using (order i).property
    · simpa using (order i₁).property
  have hP₁sub : P₁ ⊆ H := by
    intro x hx
    simp only [P₁, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa using (order i₁).property
    · simpa using
        (order (cyclicIndex (3 * k + 1) hn i₁ 1)).property

  have hgood₀' : M.eRk (P₀ ∪ C) = (4 : ℕ∞) := by
    simpa [DangerousHyperplaneEdgeGood, P₀, C, i₁, hn,
      Set.union_comm] using hgood0
  have hgood₁' : M.eRk (P₁ ∪ C) = (4 : ℕ∞) := by
    simpa [DangerousHyperplaneEdgeGood, P₁, C, i₁, hn,
      Set.union_comm] using hgood1

  have hN₀ :
      N₀.eRank = (2 : ℕ∞) ∧ N₀.Loopless := by
    simpa [N₀, C, P₀] using
      dangerous_one_good_pair_contract_complement_rank_two_loopless
        hRank hH hP₀ind hP₀sub hP₀rank hgood₀'
  have hN₁ :
      N₁.eRank = (2 : ℕ∞) ∧ N₁.Loopless := by
    simpa [N₁, C, P₁] using
      dangerous_one_good_pair_contract_complement_rank_two_loopless
        hRank hH hP₁ind hP₁sub hP₁rank hgood₁'

  obtain ⟨c₀, c₁, hcne, hB₀, hB₁⟩ :=
    RankTwoSelection.exists_common_pair_base
      N₀ N₁ (by simp [N₀, N₁, C])
      hN₀.1 hN₁.1 hN₀.2 hN₁.2

  have hc₀ : c₀ ∈ C := by
    simpa [N₀] using hB₀.subset_ground (by simp)
  have hc₁ : c₁ ∈ C := by
    simpa [N₀] using hB₀.subset_ground (by simp)

  have hAmb₀ : M.IsBase (({c₀, c₁} : Set α) ∪ P₀) :=
    ambient_isBase_of_restricted_contract_base
      hRank hP₀ind hP₀rank hN₀.1 hB₀
  have hAmb₁ : M.IsBase (({c₀, c₁} : Set α) ∪ P₁) :=
    ambient_isBase_of_restricted_contract_base
      hRank hP₁ind hP₁rank hN₁.1 hB₁

  exact ⟨c₀, c₁, hcne, by simpa [C] using hc₀, by simpa [C] using hc₁,
    hAmb₀, hAmb₁⟩

/-- Two good core edges at distance two admit a three-element complementary
path whose two consecutive pairs certify the two exceptional ambient
windows. -/
theorem dangerous_hyperplane_distance_two_good_selection
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (i : Fin (3 * k + 1))
    (hgood0 : DangerousHyperplaneEdgeGood order i)
    (hgood2 :
      DangerousHyperplaneEdgeGood order
        (cyclicIndex (3 * k + 1) (by omega) i 2)) :
    ∃ c₀ c₁ c₂ : α,
      c₀ ≠ c₁ ∧ c₁ ≠ c₂ ∧ c₀ ≠ c₂ ∧
      c₀ ∈ M.E \ H ∧ c₁ ∈ M.E \ H ∧ c₂ ∈ M.E \ H ∧
      let P₀ : Set α :=
        {(order i : α),
          (order (cyclicIndex (3 * k + 1) (by omega) i 1) : α)}
      let i₂ := cyclicIndex (3 * k + 1) (by omega) i 2
      let P₂ : Set α :=
        {(order i₂ : α),
          (order (cyclicIndex (3 * k + 1) (by omega) i₂ 1) : α)}
      M.IsBase (({c₀, c₁} : Set α) ∪ P₀) ∧
      M.IsBase (({c₁, c₂} : Set α) ∪ P₂) := by
  let hn : 0 < 3 * k + 1 := by omega
  let C : Set α := M.E \ H
  let i₂ : Fin (3 * k + 1) := cyclicIndex (3 * k + 1) hn i 2
  let P₀ : Set α :=
    {(order i : α),
      (order (cyclicIndex (3 * k + 1) hn i 1) : α)}
  let P₂ : Set α :=
    {(order i₂ : α),
      (order (cyclicIndex (3 * k + 1) hn i₂ 1) : α)}
  let N₀ : Matroid α := (M.contract P₀).restrict C
  let N₂ : Matroid α := (M.contract P₂).restrict C

  have hPair₀ :=
    dangerous_hyperplane_core_pair_indep_rank_two
      (by omega : 1 ≤ k) hH order hOrder i
  have hP₀ind : M.Indep P₀ := by
    simpa [P₀, hn] using hPair₀.1
  have hP₀rank : M.eRk P₀ = (2 : ℕ∞) := by
    simpa [P₀, hn] using hPair₀.2

  have hPair₂ :=
    dangerous_hyperplane_core_pair_indep_rank_two
      (by omega : 1 ≤ k) hH order hOrder i₂
  have hP₂ind : M.Indep P₂ := by
    simpa [P₂, i₂, hn] using hPair₂.1
  have hP₂rank : M.eRk P₂ = (2 : ℕ∞) := by
    simpa [P₂, i₂, hn] using hPair₂.2

  have hP₀sub : P₀ ⊆ H := by
    intro x hx
    simp only [P₀, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa using (order i).property
    · simpa using
        (order (cyclicIndex (3 * k + 1) hn i 1)).property
  have hP₂sub : P₂ ⊆ H := by
    intro x hx
    simp only [P₂, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa using (order i₂).property
    · simpa using
        (order (cyclicIndex (3 * k + 1) hn i₂ 1)).property

  have hgood₀' : M.eRk (P₀ ∪ C) = (4 : ℕ∞) := by
    simpa [DangerousHyperplaneEdgeGood, P₀, C, hn,
      Set.union_comm] using hgood0
  have hgood₂' : M.eRk (P₂ ∪ C) = (4 : ℕ∞) := by
    simpa [DangerousHyperplaneEdgeGood, P₂, C, i₂, hn,
      Set.union_comm] using hgood2

  have hN₀ :
      N₀.eRank = (2 : ℕ∞) ∧ N₀.Loopless := by
    simpa [N₀, C, P₀] using
      dangerous_one_good_pair_contract_complement_rank_two_loopless
        hRank hH hP₀ind hP₀sub hP₀rank hgood₀'
  have hN₂ :
      N₂.eRank = (2 : ℕ∞) ∧ N₂.Loopless := by
    simpa [N₂, C, P₂] using
      dangerous_one_good_pair_contract_complement_rank_two_loopless
        hRank hH hP₂ind hP₂sub hP₂rank hgood₂'

  have hCfin : C.Finite := by
    dsimp [C]
    exact hE.sdiff
  have hCcard : C.ncard = k + 1 := by
    dsimp [C]
    exact dangerous_complement_ncard_eq hE hEcard hH

  obtain ⟨c₀, c₁, c₂, hc01, hc12, hc02, hB₀, hB₂⟩ :=
    RankTwoSelection.exists_two_matroid_basis_path
      N₀ N₂ (by simp [N₀, N₂, C])
      (by simpa [N₀] using hCfin)
      (by simpa [N₀, hCcard])
      hN₀.1 hN₂.1 hN₀.2 hN₂.2

  have hc₀ : c₀ ∈ C := by
    simpa [N₀] using hB₀.subset_ground (by simp)
  have hc₁ : c₁ ∈ C := by
    simpa [N₀] using hB₀.subset_ground (by simp)
  have hc₂ : c₂ ∈ C := by
    simpa [N₂] using hB₂.subset_ground (by simp)

  have hAmb₀ : M.IsBase (({c₀, c₁} : Set α) ∪ P₀) :=
    ambient_isBase_of_restricted_contract_base
      hRank hP₀ind hP₀rank hN₀.1 hB₀
  have hAmb₂ : M.IsBase (({c₁, c₂} : Set α) ∪ P₂) :=
    ambient_isBase_of_restricted_contract_base
      hRank hP₂ind hP₂rank hN₂.1 hB₂

  exact ⟨c₀, c₁, c₂, hc01, hc12, hc02,
    by simpa [C] using hc₀, by simpa [C] using hc₁, by simpa [C] using hc₂,
    hAmb₀, hAmb₂⟩

end

end Rank4DangerousBranches
end HigherRankKUM
