import HigherRankKUM.BalancedWindowDecomposition
import Mathlib.Logic.Equiv.Set

/-!
# Interleaving two sequences: the aligned window criterion

Interleave a sequence `left` of `s·k` elements and a sequence `right` of `t·k` elements in `k`
blocks, each made of `s` left entries followed by `t` right entries. Every `(s+t)`-window of the
result is one of the following:

* it starts at offset `a` in the left part of block `i`: the `s`-window of `left` at `(i, a)`
  together with the `t`-window of `right` at the start of block `i`;
* it starts at offset `b` in the right part of block `i`: the `t`-window of `right` at `(i, b)`
  together with the `s`-window of `left` at the start of block `i + 1`.

So the interleaving is a cyclic basis ordering as soon as these aligned unions are bases
(`exists_cyclicBasisOrder_of_aligned_windows`). No restriction or contraction is involved.

**Rank induction by one element per block** is the case `s = 1`, `t = r - 1`. Remove `k` elements
`x_0, …, x_{k-1}` of a rank-`r` matroid on `r·k` elements and order the other `(r-1)·k` elements
cyclically. Put `x_i` in front of block `i`. The result is a cyclic basis ordering exactly when
each `x_{i+1}` is independent of the `r` windows of length `r - 1` around its slot: the `r - 1`
windows starting in block `i`, and block `i + 1` itself. No window contains two of the inserted
elements, so the conditions for different `x_i` do not interact: placing the removed elements is
a bipartite matching between elements and slots.
-/

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/-- Every `(s+t)`-window of the balanced word `(L^s R^t)^k` is an aligned union, with explicit
indices: it starts either in the left part of a block or in its right part. -/
theorem cyclicWindow_balancedBlockOrder_cases
    {P Q : Set α} {s t k : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hk : 0 < k)
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (p : Fin ((s + t) * k)) :
    (∃ (i : Fin k) (a : Fin s),
      cyclicWindow (s + t) (Nat.mul_pos (by omega) hk)
          (balancedBlockOrder hPQ left right) p =
        cyclicWindow t (Nat.mul_pos ht hk) right (blockPosition t k i ⟨0, ht⟩) ∪
          cyclicWindow s (Nat.mul_pos hs hk) left (blockPosition s k i a)) ∨
    (∃ (i : Fin k) (b : Fin t),
      cyclicWindow (s + t) (Nat.mul_pos (by omega) hk)
          (balancedBlockOrder hPQ left right) p =
        cyclicWindow t (Nat.mul_pos ht hk) right (blockPosition t k i b) ∪
          cyclicWindow s (Nat.mul_pos hs hk) left
            (blockPosition s k (cyclicIndex k hk i 1) ⟨0, hs⟩)) := by
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
    refine Or.inl ⟨i, a, ?_⟩
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
    refine Or.inr ⟨i, b, ?_⟩
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

/-- **The aligned window criterion.** If `P` and `Q` partition the ground set and every aligned
union of an `s`-window of `left` and a `t`-window of `right` is a basis, then interleaving them
as `(P^s Q^t)^k` is a cyclic basis ordering. With `s = 1` this is the reinsertion step of the
rank induction: one removed element in front of each block of `t = r - 1` elements. -/
theorem exists_cyclicBasisOrder_of_aligned_windows
    (M : Matroid α) {P Q : Set α} {s t k : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hk : 0 < k)
    (hPQ : Disjoint P Q) (hU : P ∪ Q = M.E)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (hL : ∀ (i : Fin k) (a : Fin s),
      M.IsBase
        (cyclicWindow t (Nat.mul_pos ht hk) right (blockPosition t k i ⟨0, ht⟩) ∪
          cyclicWindow s (Nat.mul_pos hs hk) left (blockPosition s k i a)))
    (hR : ∀ (i : Fin k) (b : Fin t),
      M.IsBase
        (cyclicWindow t (Nat.mul_pos ht hk) right (blockPosition t k i b) ∪
          cyclicWindow s (Nat.mul_pos hs hk) left
            (blockPosition s k (cyclicIndex k hk i 1) ⟨0, hs⟩))) :
    ∃ σ : Fin ((s + t) * k) ≃ M.E,
      CyclicBasisOrder M (s + t) (Nat.mul_pos (by omega) hk) σ := by
  let localOrder : Fin ((s + t) * k) ≃ (P ∪ Q : Set α) :=
    balancedBlockOrder hPQ left right
  let order : Fin ((s + t) * k) ≃ M.E :=
    localOrder.trans (Set.equivOfEq hU)
  refine ⟨order, ?_⟩
  intro p
  have hbase : M.IsBase
      (cyclicWindow (s + t) (Nat.mul_pos (by omega) hk)
        (balancedBlockOrder hPQ left right) p) := by
    rcases cyclicWindow_balancedBlockOrder_cases hs ht hk hPQ left right p with
      ⟨i, a, h⟩ | ⟨i, b, h⟩
    · rw [h]
      exact hL i a
    · rw [h]
      exact hR i b
  simpa only [order, localOrder, cyclicWindow, Equiv.trans_apply,
    Set.equivOfEq_apply] using hbase

end

end HigherRankKUM
