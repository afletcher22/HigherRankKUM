import HigherRankKUM.Rank4.SevenMoveTypes
import HigherRankKUM.Rank4.CyclicWindowFour

namespace HigherRankKUM
namespace Rank4EndpointSwapGeometry

open Set
open Rank4FourBlockMove
open Rank4SevenMoveTypes

noncomputable section

variable {alpha : Type*}

@[simp]
theorem cyclicIndex_modulus
    {n : ℕ} (hn : 0 < n) (i : Fin n) :
    cyclicIndex n hn i n = i := by
  apply Fin.ext
  simp [cyclicIndex, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

/-- A cyclic offset in the range 4,...,n-1 lies outside the four positions
beginning at s. -/
theorem cyclicIndex_offset_not_mem_fourBlockPositions
    {n t : ℕ} (hn : 0 < n) (s : Fin n)
    (h4t : 4 ≤ t) (htn : t < n) :
    cyclicIndex n hn s t ∉ fourBlockPositions hn s := by
  intro hmem
  change
    cyclicIndex n hn s t ∈
      Set.range (fun q : Fin 4 => cyclicIndex n hn s q.val) at hmem
  rcases hmem with ⟨q, hq⟩
  have heq :
      cyclicIndex n hn s q.val = cyclicIndex n hn s t := hq
  have hqt :=
    cyclicIndex_injective_offsets n hn s
      (by omega) htn heq
  omega

/-- Under the endpoint swap, the extreme left affected four-window is the
old consecutive three-window at s-3 plus the old element at s+3. -/
theorem endpointSwap_left_extreme_window_eq
    {E : Set alpha} {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    (sigma : Fin n ≃ E) (s : Fin n) :
    cyclicWindow 4 hn
        (applyFourBlockPerm hn (by omega) sigma s endpointSwap)
        (cyclicIndex n hn s (n - 3)) =
      insert (sigma (cyclicIndex n hn s 3) : alpha)
        (cyclicWindow 3 hn sigma
          (cyclicIndex n hn s (n - 3))) := by
  let tau :=
    applyFourBlockPerm hn (by omega) sigma s endpointSwap
  have h1 :
      cyclicIndex n hn (cyclicIndex n hn s (n - 3)) 1 =
        cyclicIndex n hn s (n - 2) := by
    rw [cyclicIndex_add]
    congr 1
    omega
  have h2 :
      cyclicIndex n hn (cyclicIndex n hn s (n - 3)) 2 =
        cyclicIndex n hn s (n - 1) := by
    rw [cyclicIndex_add]
    congr 1
    omega
  have h3 :
      cyclicIndex n hn (cyclicIndex n hn s (n - 3)) 3 = s := by
    rw [cyclicIndex_add]
    have hoff : n - 3 + 3 = n := by omega
    rw [hoff, cyclicIndex_modulus]
  have hout0 :
      tau (cyclicIndex n hn s (n - 3)) =
        sigma (cyclicIndex n hn s (n - 3)) := by
    exact applyFourBlockPerm_eq_outside
      hn (by omega) sigma s endpointSwap
      (cyclicIndex_offset_not_mem_fourBlockPositions
        hn s (by omega) (by omega))
  have hout1 :
      tau (cyclicIndex n hn s (n - 2)) =
        sigma (cyclicIndex n hn s (n - 2)) := by
    exact applyFourBlockPerm_eq_outside
      hn (by omega) sigma s endpointSwap
      (cyclicIndex_offset_not_mem_fourBlockPositions
        hn s (by omega) (by omega))
  have hout2 :
      tau (cyclicIndex n hn s (n - 1)) =
        sigma (cyclicIndex n hn s (n - 1)) := by
    exact applyFourBlockPerm_eq_outside
      hn (by omega) sigma s endpointSwap
      (cyclicIndex_offset_not_mem_fourBlockPositions
        hn s (by omega) (by omega))
  have hs :
      tau s = sigma (cyclicIndex n hn s 3) := by
    dsimp [tau]
    simpa [cyclicIndex_zero] using
      (apply_endpointSwap_local hn (by omega) sigma s).1
  rw [cyclicWindow_four_eq, cyclicWindow_three_eq]
  rw [h1, h2, h3, hout0, hout1, hout2, hs]
  ext x
  simp [or_comm, or_left_comm, or_assoc]

/-- Under the endpoint swap, the extreme right affected four-window is the
old consecutive three-window at s+4 plus the old element at s. -/
theorem endpointSwap_right_extreme_window_eq
    {E : Set alpha} {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    (sigma : Fin n ≃ E) (s : Fin n) :
    cyclicWindow 4 hn
        (applyFourBlockPerm hn (by omega) sigma s endpointSwap)
        (cyclicIndex n hn s 3) =
      insert (sigma s : alpha)
        (cyclicWindow 3 hn sigma
          (cyclicIndex n hn s 4)) := by
  let tau :=
    applyFourBlockPerm hn (by omega) sigma s endpointSwap
  have h1 :
      cyclicIndex n hn (cyclicIndex n hn s 3) 1 =
        cyclicIndex n hn s 4 := by
    rw [cyclicIndex_add]
  have h2 :
      cyclicIndex n hn (cyclicIndex n hn s 3) 2 =
        cyclicIndex n hn s 5 := by
    rw [cyclicIndex_add]
  have h3 :
      cyclicIndex n hn (cyclicIndex n hn s 3) 3 =
        cyclicIndex n hn s 6 := by
    rw [cyclicIndex_add]
  have hs3 :
      tau (cyclicIndex n hn s 3) = sigma s := by
    dsimp [tau]
    simpa [cyclicIndex_zero] using
      (apply_endpointSwap_local hn (by omega) sigma s).2.2.2
  have hout4 :
      tau (cyclicIndex n hn s 4) =
        sigma (cyclicIndex n hn s 4) := by
    exact applyFourBlockPerm_eq_outside
      hn (by omega) sigma s endpointSwap
      (cyclicIndex_offset_not_mem_fourBlockPositions
        hn s (by omega) (by omega))
  have hout5 :
      tau (cyclicIndex n hn s 5) =
        sigma (cyclicIndex n hn s 5) := by
    exact applyFourBlockPerm_eq_outside
      hn (by omega) sigma s endpointSwap
      (cyclicIndex_offset_not_mem_fourBlockPositions
        hn s (by omega) (by omega))
  have hout6 :
      tau (cyclicIndex n hn s 6) =
        sigma (cyclicIndex n hn s 6) := by
    exact applyFourBlockPerm_eq_outside
      hn (by omega) sigma s endpointSwap
      (cyclicIndex_offset_not_mem_fourBlockPositions
        hn s (by omega) (by omega))
  rw [cyclicWindow_four_eq, cyclicWindow_three_eq]
  rw [h1, h2, h3, hs3, hout4, hout5, hout6]
  ext x
  simp [or_comm, or_left_comm, or_assoc]

end

end Rank4EndpointSwapGeometry
end HigherRankKUM
