import HigherRankKUM.Rank4.FourBlockPerm

namespace HigherRankKUM
namespace Rank4FourBlockMove

open Set

noncomputable section

variable {α : Type*}

/-- A cyclic position at offset at least four from the moved start is outside
the supported four-position block, provided the offset is still below the
cycle length. -/
theorem cyclicIndex_not_mem_fourBlockPositions_of_four_le
    {n t : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (s : Fin n)
    (h4t : 4 ≤ t) (htn : t < n) :
    cyclicIndex n hn s t ∉ fourBlockPositions hn s := by
  rw [← range_fourBlockEmbedding_eq_fourBlockPositions hn h4n s]
  rintro ⟨q, hq⟩
  have hidx :
      cyclicIndex n hn s q.val = cyclicIndex n hn s t := by
    simpa [fourBlockEmbedding] using hq
  have hqt :
      q.val = t :=
    cyclicIndex_injective_offsets n hn s
      (lt_of_lt_of_le q.isLt h4n) htn hidx
  omega

/-- Explicit four-block permutations leave every cyclic offset at least four
unchanged, as long as the offset is below the cycle length. -/
theorem applyFourBlockPerm_eq_at_offset_of_four_le
    {E : Set α} {n t : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4))
    (h4t : 4 ≤ t) (htn : t < n) :
    applyFourBlockPerm hn h4n σ s π (cyclicIndex n hn s t) =
      σ (cyclicIndex n hn s t) := by
  exact applyFourBlockPerm_eq_outside hn h4n σ s π
    (cyclicIndex_not_mem_fourBlockPositions_of_four_le
      hn h4n s h4t htn)

/-- On one of the four moved coordinates, the explicit reorder reads the old
entry at the permuted local coordinate. -/
theorem applyFourBlockPerm_eq_at_local
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4))
    (q : Fin 4) :
    applyFourBlockPerm hn h4n σ s π
        (cyclicIndex n hn s q.val) =
      σ (cyclicIndex n hn s (π q).val) := by
  change
    σ (supportedFourBlockPerm hn h4n s π
      (fourBlockEmbedding hn h4n s q)) =
      σ (fourBlockEmbedding hn h4n s (π q))
  rw [supportedFourBlockPerm_apply_block]

end

end Rank4FourBlockMove
end HigherRankKUM
