import HigherRankKUM.Rank4.SevenTypeMoves
import HigherRankKUM.Rank4.FourBlockOffsets

namespace HigherRankKUM
namespace Rank4EndpointSwap

open Set
open Rank4FourBlockMove
open Rank4SevenTypeMoves

noncomputable section

variable {α : Type*}

/-- Pointwise action of the audited endpoint swap 0 <-> 3 on the moved
four-position block. -/
@[simp]
theorem apply_swap03_zero
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    applyFourBlockPerm hn h4n σ s swap03 s =
      σ (cyclicIndex n hn s 3) := by
  simpa [cyclicIndex_zero, swap03, Equiv.swap_apply_def] using
    (applyFourBlockPerm_eq_at_local
      hn h4n σ s swap03 (0 : Fin 4))

@[simp]
theorem apply_swap03_one
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    applyFourBlockPerm hn h4n σ s swap03
        (cyclicIndex n hn s 1) =
      σ (cyclicIndex n hn s 1) := by
  simpa [swap03, Equiv.swap_apply_def] using
    (applyFourBlockPerm_eq_at_local
      hn h4n σ s swap03 (1 : Fin 4))

@[simp]
theorem apply_swap03_two
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    applyFourBlockPerm hn h4n σ s swap03
        (cyclicIndex n hn s 2) =
      σ (cyclicIndex n hn s 2) := by
  simpa [swap03, Equiv.swap_apply_def] using
    (applyFourBlockPerm_eq_at_local
      hn h4n σ s swap03 (2 : Fin 4))

@[simp]
theorem apply_swap03_three
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    applyFourBlockPerm hn h4n σ s swap03
        (cyclicIndex n hn s 3) =
      σ s := by
  simpa [cyclicIndex_zero, swap03, Equiv.swap_apply_def] using
    (applyFourBlockPerm_eq_at_local
      hn h4n σ s swap03 (3 : Fin 4))

/-- Pointwise action of the audited endpoint swap 1 <-> 3. -/
@[simp]
theorem apply_swap13_zero
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    applyFourBlockPerm hn h4n σ s swap13 s = σ s := by
  simpa [cyclicIndex_zero, swap13, Equiv.swap_apply_def] using
    (applyFourBlockPerm_eq_at_local
      hn h4n σ s swap13 (0 : Fin 4))

@[simp]
theorem apply_swap13_one
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    applyFourBlockPerm hn h4n σ s swap13
        (cyclicIndex n hn s 1) =
      σ (cyclicIndex n hn s 3) := by
  simpa [swap13, Equiv.swap_apply_def] using
    (applyFourBlockPerm_eq_at_local
      hn h4n σ s swap13 (1 : Fin 4))

@[simp]
theorem apply_swap13_two
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    applyFourBlockPerm hn h4n σ s swap13
        (cyclicIndex n hn s 2) =
      σ (cyclicIndex n hn s 2) := by
  simpa [swap13, Equiv.swap_apply_def] using
    (applyFourBlockPerm_eq_at_local
      hn h4n σ s swap13 (2 : Fin 4))

@[simp]
theorem apply_swap13_three
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    applyFourBlockPerm hn h4n σ s swap13
        (cyclicIndex n hn s 3) =
      σ (cyclicIndex n hn s 1) := by
  simpa [swap13, Equiv.swap_apply_def] using
    (applyFourBlockPerm_eq_at_local
      hn h4n σ s swap13 (3 : Fin 4))

end

end Rank4EndpointSwap
end HigherRankKUM
