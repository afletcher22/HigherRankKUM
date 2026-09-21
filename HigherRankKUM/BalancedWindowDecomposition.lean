import HigherRankKUM.BalancedWindowRight

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
Every cyclic `(s+t)`-window in the balanced word `(L^s R^t)^k`
decomposes into one cyclic `t`-window of the right ordering and one cyclic
`s`-window of the left ordering.
-/
theorem cyclicWindow_balancedBlockOrder_decomposition
    {P Q : Set α} {s t k : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hk : 0 < k)
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (p : Fin ((s + t) * k)) :
    ∃ iS : Fin (s * k), ∃ iT : Fin (t * k),
      cyclicWindow (s + t) (Nat.mul_pos (by omega) hk)
          (balancedBlockOrder hPQ left right) p =
        cyclicWindow t (Nat.mul_pos ht hk) right iT ∪
          cyclicWindow s (Nat.mul_pos hs hk) left iS := by
  let z : Fin k × Fin (s + t) :=
    (blockPositionEquiv (s + t) k).symm p
  let i : Fin k := z.1
  let d : Fin (s + t) := z.2
  have hp : blockPosition (s + t) k i d = p := by
    change blockPositionEquiv (s + t) k (i, d) = p
    simpa [i, d, z] using
      (blockPositionEquiv (s + t) k).apply_symm_apply p
  by_cases hd : d.val < s
  · let a : Fin s := ⟨d.val, hd⟩
    have hda : d = Fin.castAdd t a := by
      apply Fin.ext
      rfl
    have hstart :
        p = blockPosition (s + t) k i (Fin.castAdd t a) := by
      calc
        p = blockPosition (s + t) k i d := hp.symm
        _ = blockPosition (s + t) k i (Fin.castAdd t a) :=
          congrArg (blockPosition (s + t) k i) hda
    refine ⟨blockPosition s k i a,
      blockPosition t k i ⟨0, ht⟩, ?_⟩
    calc
      cyclicWindow (s + t) (Nat.mul_pos (by omega) hk)
          (balancedBlockOrder hPQ left right) p =
        cyclicWindow (s + t) (Nat.mul_pos (by omega) hk)
          (balancedBlockOrder hPQ left right)
          (blockPosition (s + t) k i (Fin.castAdd t a)) :=
            congrArg
              (fun q => cyclicWindow (s + t)
                (Nat.mul_pos (by omega) hk)
                (balancedBlockOrder hPQ left right) q)
              hstart
      _ = cyclicWindow t (Nat.mul_pos ht hk) right
            (blockPosition t k i ⟨0, ht⟩) ∪
          cyclicWindow s (Nat.mul_pos hs hk) left
            (blockPosition s k i a) :=
        cyclicWindow_balancedBlockOrder_left_start
          hs ht hk hPQ left right i a
  · have hsd : s ≤ d.val := by omega
    let b : Fin t := ⟨d.val - s, by omega⟩
    have hdb : d = Fin.natAdd s b := by
      apply Fin.ext
      change d.val = s + (d.val - s)
      omega
    have hstart :
        p = blockPosition (s + t) k i (Fin.natAdd s b) := by
      calc
        p = blockPosition (s + t) k i d := hp.symm
        _ = blockPosition (s + t) k i (Fin.natAdd s b) :=
          congrArg (blockPosition (s + t) k i) hdb
    refine ⟨blockPosition s k (cyclicIndex k hk i 1) ⟨0, hs⟩,
      blockPosition t k i b, ?_⟩
    calc
      cyclicWindow (s + t) (Nat.mul_pos (by omega) hk)
          (balancedBlockOrder hPQ left right) p =
        cyclicWindow (s + t) (Nat.mul_pos (by omega) hk)
          (balancedBlockOrder hPQ left right)
          (blockPosition (s + t) k i (Fin.natAdd s b)) :=
            congrArg
              (fun q => cyclicWindow (s + t)
                (Nat.mul_pos (by omega) hk)
                (balancedBlockOrder hPQ left right) q)
              hstart
      _ = cyclicWindow t (Nat.mul_pos ht hk) right
            (blockPosition t k i b) ∪
          cyclicWindow s (Nat.mul_pos hs hk) left
            (blockPosition s k (cyclicIndex k hk i 1) ⟨0, hs⟩) :=
        cyclicWindow_balancedBlockOrder_right_start
          hs ht hk hPQ left right i b

end

end HigherRankKUM
