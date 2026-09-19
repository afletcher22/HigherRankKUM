import HigherRankKUM.CyclicIndex
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set

noncomputable section

/-- Two subsets of a cyclic set of 2k positions, each of size at most k-1,
cannot meet every oriented adjacency edge by a bad tail or a bad head. -/
theorem exists_cyclic_edge_avoiding_two_small_sets
    {k : ℕ} (hk : 1 ≤ k)
    (Bbad Abad : Set (Fin (2 * k)))
    (hB : Bbad.ncard ≤ k - 1)
    (hA : Abad.ncard ≤ k - 1) :
    ∃ j : Fin (2 * k),
      j ∉ Bbad ∧
      cyclicIndex (2 * k) (by omega) j 1 ∉ Abad := by
  let shift : Fin (2 * k) → Fin (2 * k) :=
    fun j => cyclicIndex (2 * k) (by omega) j 1
  have hshiftInj : Function.Injective shift :=
    cyclicIndex_injective_start (2 * k) (by omega) 1
  have hshiftSurj : Function.Surjective shift :=
    Finite.surjective_of_injective hshiftInj
  let Apre : Set (Fin (2 * k)) := shift ⁻¹' Abad
  have hApreCard : Apre.ncard = Abad.ncard := by
    apply Set.ncard_preimage_of_injective_subset_range hshiftInj
    intro a ha
    exact hshiftSurj a
  by_contra hex
  push Not at hex
  have hcover : (Set.univ : Set (Fin (2 * k))) ⊆ Bbad ∪ Apre := by
    intro j hj
    by_cases hjB : j ∈ Bbad
    · exact Or.inl hjB
    · exact Or.inr (hex j hjB)
  have hcardCover :
      (Set.univ : Set (Fin (2 * k))).ncard ≤ (Bbad ∪ Apre).ncard :=
    Set.ncard_le_ncard hcover (Set.toFinite _)
  have hunion :
      (Bbad ∪ Apre).ncard ≤ Bbad.ncard + Apre.ncard :=
    Set.ncard_union_le _ _
  have huniv :
      (Set.univ : Set (Fin (2 * k))).ncard = 2 * k := by
    simp
  rw [huniv] at hcardCover
  rw [hApreCard] at hunion
  omega

end

end Rank4DangerousBranches
end HigherRankKUM
