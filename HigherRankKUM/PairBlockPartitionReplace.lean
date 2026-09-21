import HigherRankKUM.PairBlockPartition

namespace HigherRankKUM
namespace PairBlockPartition
namespace Data

open Set

variable {α : Type*} {M : Matroid α} {N : ℕ}

/-- Replace two labelled blocks of a pair-block partition, leaving every other
block unchanged. -/
def replacedBlock
    (P : Data M N) (i j : Fin N) (L R : Set α) (k : Fin N) : Set α :=
  if k = i then L else if k = j then R else P.block k

@[simp] theorem replacedBlock_left
    (P : Data M N) (i j : Fin N) (L R : Set α) :
    P.replacedBlock i j L R i = L := by
  simp [replacedBlock]

@[simp] theorem replacedBlock_right
    (P : Data M N) {i j : Fin N} (hij : i ≠ j) (L R : Set α) :
    P.replacedBlock i j L R j = R := by
  simp [replacedBlock, hij, Ne.symm hij]

@[simp] theorem replacedBlock_other
    (P : Data M N) {i j k : Fin N} (hki : k ≠ i) (hkj : k ≠ j)
    (L R : Set α) :
    P.replacedBlock i j L R k = P.block k := by
  simp [replacedBlock, hki, hkj]

private theorem replacement_left_subset_ground
    (P : Data M N) {i j : Fin N} {L R : Set α}
    (hunion : L ∪ R = P.block i ∪ P.block j) :
    L ⊆ M.E := by
  intro x hx
  have hxU : x ∈ P.block i ∪ P.block j := by
    rw [← hunion]
    exact Or.inl hx
  rcases hxU with hxi | hxj
  · exact P.subset_ground i hxi
  · exact P.subset_ground j hxj

private theorem replacement_right_subset_ground
    (P : Data M N) {i j : Fin N} {L R : Set α}
    (hunion : L ∪ R = P.block i ∪ P.block j) :
    R ⊆ M.E := by
  intro x hx
  have hxU : x ∈ P.block i ∪ P.block j := by
    rw [← hunion]
    exact Or.inr hx
  rcases hxU with hxi | hxj
  · exact P.subset_ground i hxi
  · exact P.subset_ground j hxj

private theorem replacement_left_disjoint_old
    (P : Data M N) {i j k : Fin N} {L R : Set α}
    (hki : k ≠ i) (hkj : k ≠ j)
    (hunion : L ∪ R = P.block i ∪ P.block j) :
    Disjoint L (P.block k) := by
  rw [Set.disjoint_left]
  intro x hxL hxk
  have hxU : x ∈ P.block i ∪ P.block j := by
    rw [← hunion]
    exact Or.inl hxL
  rcases hxU with hxi | hxj
  · exact Set.disjoint_left.1 (P.disjoint (Ne.symm hki)) hxi hxk
  · exact Set.disjoint_left.1 (P.disjoint (Ne.symm hkj)) hxj hxk

private theorem replacement_right_disjoint_old
    (P : Data M N) {i j k : Fin N} {L R : Set α}
    (hki : k ≠ i) (hkj : k ≠ j)
    (hunion : L ∪ R = P.block i ∪ P.block j) :
    Disjoint R (P.block k) := by
  rw [Set.disjoint_left]
  intro x hxR hxk
  have hxU : x ∈ P.block i ∪ P.block j := by
    rw [← hunion]
    exact Or.inr hxR
  rcases hxU with hxi | hxj
  · exact Set.disjoint_left.1 (P.disjoint (Ne.symm hki)) hxi hxk
  · exact Set.disjoint_left.1 (P.disjoint (Ne.symm hkj)) hxj hxk

/-- Replacing two distinct pair blocks by another disjoint `2+2` partition of
their same four-element union preserves the global pair-block partition.

The only genuinely new hypotheses are that the replacement blocks each have
size two, are disjoint, and have the same union as the two old blocks. Ground
containment, disjointness from untouched blocks, and global coverage follow
from the original partition. -/
def replaceTwo
    (P : Data M N) (i j : Fin N) (hij : i ≠ j)
    (L R : Set α)
    (hLcard : L.encard = 2) (hRcard : R.encard = 2)
    (hLR : Disjoint L R)
    (hunion : L ∪ R = P.block i ∪ P.block j) :
    Data M N where
  block := P.replacedBlock i j L R
  card_two := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa using hLcard
    by_cases hkj : k = j
    · subst k
      simpa [hij, Ne.symm hij] using hRcard
    · simpa [replacedBlock, hki, hkj] using P.card_two k
  subset_ground := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa using replacement_left_subset_ground P hunion
    by_cases hkj : k = j
    · subst k
      simpa [hij, Ne.symm hij] using replacement_right_subset_ground P hunion
    · simpa [replacedBlock, hki, hkj] using P.subset_ground k
  disjoint := by
    intro k l hkl
    by_cases hki : k = i
    · subst k
      by_cases hlj : l = j
      · subst l
        simpa [hij, Ne.symm hij] using hLR
      have hli : l ≠ i := by
        intro hli
        exact hkl hli.symm
      simpa [replacedBlock, hli, hlj] using
        replacement_left_disjoint_old P hli hlj hunion
    by_cases hkj : k = j
    · subst k
      by_cases hli : l = i
      · subst l
        simpa [hij, Ne.symm hij] using hLR.symm
      have hlj : l ≠ j := by
        intro hlj
        exact hkl hlj.symm
      simpa [replacedBlock, hli, hlj, hij, Ne.symm hij] using
        replacement_right_disjoint_old P hli hlj hunion
    by_cases hli : l = i
    · subst l
      simpa [replacedBlock, hki, hkj] using
        (replacement_left_disjoint_old P hki hkj hunion).symm
    by_cases hlj : l = j
    · subst l
      simpa [replacedBlock, hki, hkj, hij, Ne.symm hij] using
        (replacement_right_disjoint_old P hki hkj hunion).symm
    · simpa [replacedBlock, hki, hkj, hli, hlj] using P.disjoint hkl
  cover := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
      by_cases hki : k = i
      · subst k
        have hxL : x ∈ L := by simpa using hxk
        exact replacement_left_subset_ground P hunion hxL
      by_cases hkj : k = j
      · subst k
        have hxR : x ∈ R := by simpa [hij, Ne.symm hij] using hxk
        exact replacement_right_subset_ground P hunion hxR
      · have hxold : x ∈ P.block k := by
          simpa [replacedBlock, hki, hkj] using hxk
        exact P.subset_ground k hxold
    · intro hx
      have hxOldUnion : x ∈ ⋃ k, P.block k := by
        rw [P.cover]
        exact hx
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxOldUnion
      by_cases hki : k = i
      · subst k
        have hxU : x ∈ P.block i ∪ P.block j := Or.inl hxk
        have hxNew : x ∈ L ∪ R := by
          rw [hunion]
          exact hxU
        rcases hxNew with hxL | hxR
        · exact Set.mem_iUnion.2 ⟨i, by simpa using hxL⟩
        · exact Set.mem_iUnion.2 ⟨j, by simpa [hij, Ne.symm hij] using hxR⟩
      by_cases hkj : k = j
      · subst k
        have hxU : x ∈ P.block i ∪ P.block j := Or.inr hxk
        have hxNew : x ∈ L ∪ R := by
          rw [hunion]
          exact hxU
        rcases hxNew with hxL | hxR
        · exact Set.mem_iUnion.2 ⟨i, by simpa using hxL⟩
        · exact Set.mem_iUnion.2 ⟨j, by simpa [hij, Ne.symm hij] using hxR⟩
      · exact Set.mem_iUnion.2 ⟨k, by simpa [replacedBlock, hki, hkj] using hxk⟩

end Data
end PairBlockPartition
end HigherRankKUM
