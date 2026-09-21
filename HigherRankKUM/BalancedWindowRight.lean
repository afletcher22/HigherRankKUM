import HigherRankKUM.BalancedWindow

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
If an `(s+t)`-window starts in the right segment of a balanced block, its
right entries form the cyclic `t`-window beginning at that right offset,
while its left entries form one cyclic `s`-window beginning at offset zero
in the next block.
-/
theorem cyclicWindow_balancedBlockOrder_right_start
    {P Q : Set α} {s t k : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hk : 0 < k)
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (i : Fin k) (b : Fin t) :
    cyclicWindow (s + t) (Nat.mul_pos (by omega) hk)
        (balancedBlockOrder hPQ left right)
        (blockPosition (s + t) k i (Fin.natAdd s b)) =
      cyclicWindow t (Nat.mul_pos ht hk) right
          (blockPosition t k i b) ∪
        cyclicWindow s (Nat.mul_pos hs hk) left
          (blockPosition s k (cyclicIndex k hk i 1) ⟨0, hs⟩) := by
  ext x
  simp only [cyclicWindow, Set.mem_range, Set.mem_union]
  constructor
  · rintro ⟨q, rfl⟩
    by_cases hright : b.val + q.val < t
    · left
      let qt : Fin t := ⟨q.val, by omega⟩
      refine ⟨qt, ?_⟩
      symm
      have hout := cyclicIndex_blockPosition_same
        (s + t) k (by omega) hk i (Fin.natAdd s b) q.val
          (by
            change s + b.val + q.val < s + t
            omega)
      have hsrc := cyclicIndex_blockPosition_same
        t k ht hk i b qt.val (by simp [qt]; omega)
      rw [hout, hsrc]
      have heval := balancedBlockOrder_apply_right_of_le
        hPQ left right i
        (⟨s + b.val + q.val, by omega⟩ : Fin (s + t))
        (by
          change s ≤ s + b.val + q.val
          omega)
      have hoff : s + b.val + q.val - s = b.val + q.val := by
        omega
      simpa [qt, hoff] using heval
    · by_cases hleft : b.val + q.val < t + s
      · right
        let qs : Fin s := ⟨b.val + q.val - t, by omega⟩
        refine ⟨qs, ?_⟩
        symm
        have hout := cyclicIndex_blockPosition_next
          (s + t) k (by omega) hk i (Fin.natAdd s b) q.val q.isLt
            (by
              change s + t ≤ s + b.val + q.val
              omega)
        have hsrc := cyclicIndex_blockPosition_same
          s k hs hk (cyclicIndex k hk i 1) (⟨0, hs⟩ : Fin s) qs.val
            (by simp [qs]; omega)
        rw [hout, hsrc]
        have hres :
            s + b.val + q.val - (s + t) = b.val + q.val - t := by
          omega
        have heval := balancedBlockOrder_apply_left_of_lt
          hPQ left right (cyclicIndex k hk i 1)
          (⟨b.val + q.val - t, by omega⟩ : Fin (s + t))
          (by
            change b.val + q.val - t < s
            omega)
        simpa [qs, hres] using heval
      · left
        let qt : Fin t := ⟨q.val - s, by omega⟩
        refine ⟨qt, ?_⟩
        symm
        have hout := cyclicIndex_blockPosition_next
          (s + t) k (by omega) hk i (Fin.natAdd s b) q.val q.isLt
            (by
              change s + t ≤ s + b.val + q.val
              omega)
        have hsrc := cyclicIndex_blockPosition_next
          t k ht hk i b qt.val qt.isLt
            (by simp [qt]; omega)
        rw [hout, hsrc]
        have houtres :
            s + b.val + q.val - (s + t) = b.val + q.val - t := by
          omega
        have hsrcres :
            b.val + (q.val - s) - t = b.val + q.val - (s + t) := by
          omega
        have hoff :
            b.val + q.val - t - s = b.val + q.val - (s + t) := by
          omega
        have heval := balancedBlockOrder_apply_right_of_le
          hPQ left right (cyclicIndex k hk i 1)
          (⟨b.val + q.val - t, by omega⟩ : Fin (s + t))
          (by
            change s ≤ b.val + q.val - t
            omega)
        simpa [qt, houtres, hsrcres, hoff] using heval
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · by_cases hsame : b.val + j.val < t
      · let q : Fin (s + t) := ⟨j.val, by omega⟩
        refine ⟨q, ?_⟩
        have hout := cyclicIndex_blockPosition_same
          (s + t) k (by omega) hk i (Fin.natAdd s b) q.val
            (by
              change s + b.val + q.val < s + t
              simp [q]
              omega)
        have hsrc := cyclicIndex_blockPosition_same
          t k ht hk i b j.val hsame
        rw [hout, hsrc]
        have heval := balancedBlockOrder_apply_right_of_le
          hPQ left right i
          (⟨s + b.val + j.val, by omega⟩ : Fin (s + t))
          (by
            change s ≤ s + b.val + j.val
            omega)
        have hoff : s + b.val + j.val - s = b.val + j.val := by
          omega
        simpa [q, hoff] using heval
      · let q : Fin (s + t) := ⟨s + j.val, by omega⟩
        refine ⟨q, ?_⟩
        have hout := cyclicIndex_blockPosition_next
          (s + t) k (by omega) hk i (Fin.natAdd s b) q.val q.isLt
            (by
              change s + t ≤ s + b.val + q.val
              simp [q]
              omega)
        have hsrc := cyclicIndex_blockPosition_next
          t k ht hk i b j.val j.isLt (by omega)
        rw [hout, hsrc]
        have hres :
            s + b.val + q.val - (s + t) = s + (b.val + j.val - t) := by
          simp [q]
          omega
        have heval := balancedBlockOrder_apply_right_of_le
          hPQ left right (cyclicIndex k hk i 1)
          (⟨s + (b.val + j.val - t), by omega⟩ : Fin (s + t))
          (by
            change s ≤ s + (b.val + j.val - t)
            omega)
        simpa [q, hres] using heval
    · let q : Fin (s + t) := ⟨t - b.val + j.val, by omega⟩
      refine ⟨q, ?_⟩
      have hout := cyclicIndex_blockPosition_next
        (s + t) k (by omega) hk i (Fin.natAdd s b) q.val q.isLt
          (by
            change s + t ≤ s + b.val + q.val
            simp [q]
            omega)
      have hsrc := cyclicIndex_blockPosition_same
        s k hs hk (cyclicIndex k hk i 1) (⟨0, hs⟩ : Fin s) j.val
          (by
            change 0 + j.val < s
            omega)
      rw [hout, hsrc]
      have hres :
          s + b.val + q.val - (s + t) = j.val := by
        simp [q]
        omega
      have heval := balancedBlockOrder_apply_left_of_lt
        hPQ left right (cyclicIndex k hk i 1)
        (⟨j.val, by omega⟩ : Fin (s + t))
        (by
          change j.val < s
          exact j.isLt)
      simpa [hres] using heval

end

end HigherRankKUM
