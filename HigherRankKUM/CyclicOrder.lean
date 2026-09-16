import HigherRankKUM.CyclicIndex
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Tactic

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/-- The set of `r` cyclically consecutive entries beginning at `i`. -/
def cyclicWindow
    {E : Set α} {n : ℕ}
    (r : ℕ) (hn : 0 < n)
    (σ : Fin n ≃ E) (i : Fin n) : Set α :=
  Set.range fun j : Fin r =>
    (σ (cyclicIndex n hn i j.val) : α)

/-- An arbitrary-rank cyclic basis ordering. -/
def CyclicBasisOrder
    (M : Matroid α) (r : ℕ)
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) : Prop :=
  ∀ i : Fin n, M.IsBase (cyclicWindow r hn σ i)

end

end HigherRankKUM
