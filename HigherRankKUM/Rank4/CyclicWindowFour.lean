import HigherRankKUM.CyclicOrder
import Mathlib.Tactic

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/-- A length-two cyclic window is exactly its two successive entries. -/
theorem cyclicWindow_two_eq
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow 2 hn σ i =
      ({(σ i : α), (σ (cyclicIndex n hn i 1) : α)} : Set α) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [cyclicWindow, cyclicIndex_zero]
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact ⟨0, by simp [cyclicIndex_zero]⟩
    · subst x
      exact ⟨1, rfl⟩

/-- A length-four cyclic window is exactly the set of the four explicit
successive entries.  This packages the `Fin 4` range bookkeeping used
throughout the direct rank-four constructions. -/
theorem cyclicWindow_four_eq
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow 4 hn σ i =
      ({(σ i : α),
        (σ (cyclicIndex n hn i 1) : α),
        (σ (cyclicIndex n hn i 2) : α),
        (σ (cyclicIndex n hn i 3) : α)} : Set α) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [cyclicWindow, cyclicIndex_zero]
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx
    · subst x
      exact ⟨0, by simp [cyclicIndex_zero]⟩
    · subst x
      exact ⟨1, rfl⟩
    · subst x
      exact ⟨2, rfl⟩
    · subst x
      exact ⟨3, rfl⟩

/-- Rank-four cyclic-basis ordering can be checked by the explicit four
successive entries at every start. -/
theorem cyclicBasisOrder_four_iff
    {M : Matroid α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ M.E) :
    CyclicBasisOrder M 4 hn σ ↔
      ∀ i : Fin n,
        M.IsBase
          ({(σ i : α),
            (σ (cyclicIndex n hn i 1) : α),
            (σ (cyclicIndex n hn i 2) : α),
            (σ (cyclicIndex n hn i 3) : α)} : Set α) := by
  constructor
  · intro h i
    simpa [cyclicWindow_four_eq] using h i
  · intro h i
    rw [cyclicWindow_four_eq]
    exact h i

end

end HigherRankKUM
