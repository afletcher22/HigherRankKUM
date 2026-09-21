import HigherRankKUM.Rank4.SevenMoveTypes
import HigherRankKUM.Rank4.BlockerCycle

namespace HigherRankKUM
namespace Rank4Swap23BlockerLocality

open Set
open Rank4FourBlockMove
open Rank4SevenMoveTypes

noncomputable section

variable {α : Type*}

/-- A cyclic position at offset four is outside the four-position block
starting at `s`, provided the cycle has at least five positions. -/
theorem cyclicIndex_four_not_mem_fourBlockPositions
    {n : ℕ} (hn : 0 < n) (h5n : 5 ≤ n) (s : Fin n) :
    cyclicIndex n hn s 4 ∉ fourBlockPositions hn s := by
  intro hmem
  rw [← range_fourBlockEmbedding_eq_fourBlockPositions hn (by omega) s] at hmem
  rcases hmem with ⟨q, hq⟩
  have hEq :
      cyclicIndex n hn s 4 = cyclicIndex n hn s q.val := by
    simpa using hq.symm
  have hOff : 4 = q.val :=
    cyclicIndex_injective_offsets n hn s (by omega) (by omega) hEq
  omega

/-- Swapping local positions 2 and 3 leaves the length-three window starting
one position later unchanged as a set: that window contains both swapped
entries. -/
theorem cyclicWindow_three_swap23_shift_one_eq
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    cyclicWindow 3 hn
        (applyFourBlockPerm hn h4n σ s swap23)
        (cyclicIndex n hn s 1) =
      cyclicWindow 3 hn σ (cyclicIndex n hn s 1) := by
  rw [cyclicWindow_three_eq, cyclicWindow_three_eq]
  simp only [cyclicIndex_add]
  have h1 :=
    applyFourBlockPerm_apply_local hn h4n σ s swap23 (1 : Fin 4)
  have h2 :=
    applyFourBlockPerm_apply_local hn h4n σ s swap23 (2 : Fin 4)
  have h3 :=
    applyFourBlockPerm_apply_local hn h4n σ s swap23 (3 : Fin 4)
  have hp := swap23_table
  rcases hp with ⟨hp0, hp1, hp2, hp3⟩
  simp only [hp1] at h1
  simp only [hp2] at h2
  simp only [hp3] at h3
  rw [h1, h2, h3]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Swapping local positions 2 and 3 also leaves the length-three window
starting two positions later unchanged as a set.  Its first two entries are
the swapped pair and its last entry lies just outside the moved block. -/
theorem cyclicWindow_three_swap23_shift_two_eq
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h5n : 5 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    cyclicWindow 3 hn
        (applyFourBlockPerm hn (by omega) σ s swap23)
        (cyclicIndex n hn s 2) =
      cyclicWindow 3 hn σ (cyclicIndex n hn s 2) := by
  rw [cyclicWindow_three_eq, cyclicWindow_three_eq]
  simp only [cyclicIndex_add]
  have h2 :=
    applyFourBlockPerm_apply_local hn (by omega) σ s swap23 (2 : Fin 4)
  have h3 :=
    applyFourBlockPerm_apply_local hn (by omega) σ s swap23 (3 : Fin 4)
  have hp := swap23_table
  rcases hp with ⟨hp0, hp1, hp2, hp3⟩
  simp only [hp2] at h2
  simp only [hp3] at h3
  have h4out :
      cyclicIndex n hn s 4 ∉ fourBlockPositions hn s :=
    cyclicIndex_four_not_mem_fourBlockPositions hn h5n s
  have h4 :=
    applyFourBlockPerm_eq_outside hn (by omega) σ s swap23 h4out
  rw [h2, h3, h4]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Consequently the blocker predicate is unchanged at start `s+1` by a
`swap23` reorder. -/
theorem blockerAt_swap23_shift_one_iff
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (e : α) (s : Fin n) :
    Rank4BlockerCycle.blockerAt M hn
        (applyFourBlockPerm hn h4n σ s swap23) e
        (cyclicIndex n hn s 1) ↔
      Rank4BlockerCycle.blockerAt M hn σ e
        (cyclicIndex n hn s 1) := by
  unfold Rank4BlockerCycle.blockerAt
  rw [cyclicWindow_three_swap23_shift_one_eq hn h4n σ s]

/-- The blocker predicate is likewise unchanged at start `s+2`. -/
theorem blockerAt_swap23_shift_two_iff
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h5n : 5 ≤ n)
    (σ : Fin n ≃ E) (e : α) (s : Fin n) :
    Rank4BlockerCycle.blockerAt M hn
        (applyFourBlockPerm hn (by omega) σ s swap23) e
        (cyclicIndex n hn s 2) ↔
      Rank4BlockerCycle.blockerAt M hn σ e
        (cyclicIndex n hn s 2) := by
  unfold Rank4BlockerCycle.blockerAt
  rw [cyclicWindow_three_swap23_shift_two_eq hn h5n σ s]

end

end Rank4Swap23BlockerLocality
end HigherRankKUM
