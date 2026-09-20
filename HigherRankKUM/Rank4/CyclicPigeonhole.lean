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


/-- On a cycle of length 3k+1, if every three consecutive positions contain
a good position, then some two good positions are either adjacent or exactly
two steps apart.

Equivalently, a cyclic binary word of length 3k+1 with no BBB factor cannot
avoid both GG and G?G. This is the combinatorial core of the
dangerous-hyperplane extension argument. -/
theorem exists_adjacent_or_distance_two_good
    {k : ℕ} (hk : 1 ≤ k)
    (Good : Fin (3 * k + 1) → Prop)
    (hNoThreeBad :
      ∀ i : Fin (3 * k + 1),
        Good i ∨
        Good (cyclicIndex (3 * k + 1) (by omega) i 1) ∨
        Good (cyclicIndex (3 * k + 1) (by omega) i 2)) :
    ∃ i : Fin (3 * k + 1),
      (Good i ∧ Good (cyclicIndex (3 * k + 1) (by omega) i 1)) ∨
      (Good i ∧ Good (cyclicIndex (3 * k + 1) (by omega) i 2)) := by
  classical
  let n := 3 * k + 1
  let hn : 0 < n := by
    dsimp [n]
    omega
  let shift1 : Fin n → Fin n := fun i => cyclicIndex n hn i 1
  let shift2 : Fin n → Fin n := fun i => cyclicIndex n hn i 2
  let G : Set (Fin n) := {i | Good i}
  let A1 : Set (Fin n) := shift1 ⁻¹' G
  let A2 : Set (Fin n) := shift2 ⁻¹' G

  by_contra hExist
  push_neg at hExist
  have hNoAdj : ∀ i : Fin n, ¬ (Good i ∧ Good (shift1 i)) := by
    intro i h
    exact (hExist i).1 h.1 h.2
  have hNoTwo : ∀ i : Fin n, ¬ (Good i ∧ Good (shift2 i)) := by
    intro i h
    exact (hExist i).2 h.1 h.2

  have hshift1_inj : Function.Injective shift1 := by
    dsimp [shift1]
    exact cyclicIndex_injective_start n hn 1
  have hshift2_inj : Function.Injective shift2 := by
    dsimp [shift2]
    exact cyclicIndex_injective_start n hn 2
  have hshift1_surj : Function.Surjective shift1 :=
    Finite.surjective_of_injective hshift1_inj
  have hshift2_surj : Function.Surjective shift2 :=
    Finite.surjective_of_injective hshift2_inj

  have hA1card : A1.ncard = G.ncard := by
    dsimp [A1]
    exact Set.ncard_preimage_of_injective_subset_range
      hshift1_inj (fun g hg => hshift1_surj g)
  have hA2card : A2.ncard = G.ncard := by
    dsimp [A2]
    exact Set.ncard_preimage_of_injective_subset_range
      hshift2_inj (fun g hg => hshift2_surj g)

  have hGA1 : Disjoint G A1 := by
    rw [Set.disjoint_left]
    intro i hiG hiA1
    exact hNoAdj i ⟨hiG, hiA1⟩
  have hGA2 : Disjoint G A2 := by
    rw [Set.disjoint_left]
    intro i hiG hiA2
    exact hNoTwo i ⟨hiG, hiA2⟩
  have hA1A2 : Disjoint A1 A2 := by
    rw [Set.disjoint_left]
    intro i hi1 hi2
    have hgood1 : Good (shift1 i) := hi1
    have hgood2 : Good (shift2 i) := hi2
    have hshift : shift1 (shift1 i) = shift2 i := by
      dsimp [shift1, shift2]
      simpa [cyclicIndex_add]
    exact hNoAdj (shift1 i) ⟨hgood1, by simpa [hshift] using hgood2⟩

  have hcover : (Set.univ : Set (Fin n)) ⊆ G ∪ (A1 ∪ A2) := by
    intro i hi
    have htri := hNoThreeBad i
    rcases htri with hiG | hi1 | hi2
    · exact Or.inl hiG
    · exact Or.inr (Or.inl hi1)
    · exact Or.inr (Or.inr hi2)

  have hUnionEq : G ∪ (A1 ∪ A2) = (Set.univ : Set (Fin n)) := by
    exact Set.Subset.antisymm (by simp) hcover

  have hG_A12 : Disjoint G (A1 ∪ A2) := by
    exact hGA1.union_right hGA2

  have hcardA12 :
      (A1 ∪ A2).ncard = A1.ncard + A2.ncard :=
    Set.ncard_union_eq hA1A2 (Set.toFinite _) (Set.toFinite _)
  have hcardAll :
      (G ∪ (A1 ∪ A2)).ncard =
        G.ncard + (A1 ∪ A2).ncard :=
    Set.ncard_union_eq hG_A12 (Set.toFinite _) (Set.toFinite _)
  have huniv :
      (Set.univ : Set (Fin n)).ncard = n := by
    simp

  rw [hUnionEq, huniv, hcardA12, hA1card, hA2card] at hcardAll
  dsimp [n] at hcardAll
  omega

end

end Rank4DangerousBranches
end HigherRankKUM
