import HigherRankKUM.Rank4.LocalExchangeObstruction
import HigherRankKUM.Rank4.CyclicWindowFour

namespace HigherRankKUM
namespace Rank4MiddleSwapRigidity

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

private theorem orderValue_ne_of_offset_ne
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (i : Fin n)
    {a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (σ (cyclicIndex n hn i a) : α) ≠
      (σ (cyclicIndex n hn i b) : α) := by
  intro h
  apply hab
  apply cyclicIndex_injective_offsets n hn i ha hb
  apply σ.injective
  apply Subtype.ext
  exact h

/-- The left rank-four window contains the entry at offset three but not the
entry at offset four, provided the cycle has length at least eight. -/
theorem left_boundary_membership
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h8n : 8 ≤ n)
    (σ : Fin n ≃ E) (i : Fin n) :
    (σ (cyclicIndex n hn i 3) : α) ∈ cyclicWindow 4 hn σ i ∧
      (σ (cyclicIndex n hn i 4) : α) ∉ cyclicWindow 4 hn σ i := by
  rw [cyclicWindow_four_eq]
  constructor
  · exact Or.inr (Or.inr (Or.inr rfl))
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 4) (b := 0) (by omega) (by omega) (by omega)) h
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 4) (b := 1) (by omega) (by omega) (by omega)) h
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 4) (b := 2) (by omega) (by omega) (by omega)) h
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 4) (b := 3) (by omega) (by omega) (by omega)) h

/-- Symmetrically, the rank-four window beginning four steps later contains
the offset-four entry but not the offset-three entry. -/
theorem right_boundary_membership
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h8n : 8 ≤ n)
    (σ : Fin n ≃ E) (i : Fin n) :
    (σ (cyclicIndex n hn i 4) : α) ∈
        cyclicWindow 4 hn σ (cyclicIndex n hn i 4) ∧
      (σ (cyclicIndex n hn i 3) : α) ∉
        cyclicWindow 4 hn σ (cyclicIndex n hn i 4) := by
  rw [cyclicWindow_four_eq]
  simp only [cyclicIndex_add]
  constructor
  · exact Or.inl (by simp)
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 3) (b := 4) (by omega) (by omega) (by omega)) (by simpa using h)
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 3) (b := 5) (by omega) (by omega) (by omega)) (by simpa using h)
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 3) (b := 6) (by omega) (by omega) (by omega)) (by simpa using h)
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 3) (b := 7) (by omega) (by omega) (by omega)) (by simpa using h)

/-- Exact two-boundary obstruction for swapping the adjacent entries at cyclic
offsets three and four.

The original CBO gives two bases:
* the window beginning at `i`, which contains the offset-three entry `x`;
* the window beginning at `i+4`, which contains the offset-four entry `y`.

Replacing `x` by `y` on the left and `y` by `x` on the right fails
exactly when one of the retained rank-three boundary sets spans the incoming
element. -/
theorem middle_swap_boundary_failure_iff_closure_obstruction
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h8n : 8 ≤ n)
    (σ : Fin n ≃ E)
    (hCBO : CyclicBasisOrder M 4 hn σ)
    (i : Fin n) :
    let x : α := (σ (cyclicIndex n hn i 3) : α)
    let y : α := (σ (cyclicIndex n hn i 4) : α)
    let B := cyclicWindow 4 hn σ i
    let L := cyclicWindow 4 hn σ (cyclicIndex n hn i 4)
    (¬ (M.IsBase (insert y (B \ {x})) ∧
        M.IsBase (insert x (L \ {y})))) ↔
      y ∈ M.closure (B \ {x}) ∨
      x ∈ M.closure (L \ {y}) := by
  dsimp
  have hleft := left_boundary_membership hn h8n σ i
  have hright := right_boundary_membership hn h8n σ i
  exact
    Rank4LocalExchangeObstruction.not_both_exchange_bases_iff_closure_obstruction
      (hCBO i)
      (hCBO (cyclicIndex n hn i 4))
      hleft.1 hleft.2 hright.1 hright.2

end

end Rank4MiddleSwapRigidity
end HigherRankKUM
