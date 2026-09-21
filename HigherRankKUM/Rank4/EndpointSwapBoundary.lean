import HigherRankKUM.Rank4.EndpointSwapValues
import HigherRankKUM.LocalExchangeClosure
import HigherRankKUM.Rank4.CyclicWindowFour

namespace HigherRankKUM
namespace Rank4EndpointSwap

open Set
open Rank4FourBlockMove
open Rank4SevenTypeMoves

noncomputable section

variable {α : Type*}

/-- Under swap03, the boundary window beginning three positions after the
moved block start replaces the old offset-3 element by the old offset-0
element; offsets 4,5,6 are untouched. -/
theorem swap03_window_plus_three_eq
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) :
    cyclicWindow 4 hn
        (applyFourBlockPerm hn (by omega) σ s swap03)
        (cyclicIndex n hn s 3) =
      ({(σ s : α),
        (σ (cyclicIndex n hn s 4) : α),
        (σ (cyclicIndex n hn s 5) : α),
        (σ (cyclicIndex n hn s 6) : α)} : Set α) := by
  have h4 :=
    applyFourBlockPerm_eq_at_offset_of_four_le
      hn (by omega) σ s swap03 (t := 4) (by omega) (by omega)
  have h5 :=
    applyFourBlockPerm_eq_at_offset_of_four_le
      hn (by omega) σ s swap03 (t := 5) (by omega) (by omega)
  have h6 :=
    applyFourBlockPerm_eq_at_offset_of_four_le
      hn (by omega) σ s swap03 (t := 6) (by omega) (by omega)
  rw [cyclicWindow_four_eq]
  simp only [cyclicIndex_add]
  norm_num
  rw [apply_swap03_three, h4, h5, h6]

/-- The original boundary window at start s+3 consists of the old offset-3
endpoint and the unchanged offsets 4,5,6. -/
theorem original_window_plus_three_eq
    {E : Set α} {n : ℕ}
    (hn : 0 < n)
    (σ : Fin n ≃ E) (s : Fin n) :
    cyclicWindow 4 hn σ (cyclicIndex n hn s 3) =
      ({(σ (cyclicIndex n hn s 3) : α),
        (σ (cyclicIndex n hn s 4) : α),
        (σ (cyclicIndex n hn s 5) : α),
        (σ (cyclicIndex n hn s 6) : α)} : Set α) := by
  rw [cyclicWindow_four_eq]
  simp only [cyclicIndex_add]
  norm_num

/-- If the swap03 rightmost boundary window becomes dependent, the incoming
old offset-0 endpoint is spanned by the unchanged three-element boundary core
at offsets 4,5,6. -/
theorem swap03_plus_three_dep_forces_closure
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n)
    (hCBO : CyclicBasisOrder M 4 hn σ)
    (hdep :
      M.Dep
        (cyclicWindow 4 hn
          (applyFourBlockPerm hn (by omega) σ s swap03)
          (cyclicIndex n hn s 3))) :
    (σ s : α) ∈
      M.closure
        ({(σ (cyclicIndex n hn s 4) : α),
          (σ (cyclicIndex n hn s 5) : α),
          (σ (cyclicIndex n hn s 6) : α)} : Set α) := by
  let C : Set α :=
    {(σ (cyclicIndex n hn s 4) : α),
     (σ (cyclicIndex n hn s 5) : α),
     (σ (cyclicIndex n hn s 6) : α)}
  have hB :
      M.IsBase
        (insert (σ (cyclicIndex n hn s 3) : α) C) := by
    have h := hCBO (cyclicIndex n hn s 3)
    rw [original_window_plus_three_eq hn σ s] at h
    simpa [C] using h
  have ha4 :
      (σ s : α) ≠ (σ (cyclicIndex n hn s 4) : α) := by
    simpa [cyclicIndex_zero] using
      (cyclicOrder_value_ne_of_offsets_ne
        hn σ s (a := 0) (b := 4) (by omega) (by omega) (by omega))
  have ha5 :
      (σ s : α) ≠ (σ (cyclicIndex n hn s 5) : α) := by
    simpa [cyclicIndex_zero] using
      (cyclicOrder_value_ne_of_offsets_ne
        hn σ s (a := 0) (b := 5) (by omega) (by omega) (by omega))
  have ha6 :
      (σ s : α) ≠ (σ (cyclicIndex n hn s 6) : α) := by
    simpa [cyclicIndex_zero] using
      (cyclicOrder_value_ne_of_offsets_ne
        hn σ s (a := 0) (b := 6) (by omega) (by omega) (by omega))
  have haC : (σ s : α) ∉ C := by
    simp [C, ha4, ha5, ha6]
  have hdep' :
      M.Dep (insert (σ s : α) C) := by
    rw [swap03_window_plus_three_eq hn h7n σ s] at hdep
    simpa [C] using hdep
  exact LocalExchangeClosure.mem_closure_of_failed_base_exchange
    hB haC hdep'

end

end Rank4EndpointSwap
end HigherRankKUM
