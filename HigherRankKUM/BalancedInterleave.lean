import HigherRankKUM.GenericGluing
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/-- Enumerate `k` blocks of length `r`, with the offset varying fastest. -/
def blockPositionEquiv (r k : ℕ) :
    Fin k × Fin r ≃ Fin (r * k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm r k)).symm

/-- The position of offset `j` in block `i`. -/
def blockPosition (r k : ℕ) (i : Fin k) (j : Fin r) :
    Fin (r * k) :=
  blockPositionEquiv r k (i, j)

@[simp] theorem blockPosition_val
    (r k : ℕ) (i : Fin k) (j : Fin r) :
    (blockPosition r k i j).val = j.val + r * i.val := by
  rfl

/-- A cyclic shift that stays inside a block is just an offset shift. -/
theorem cyclicIndex_blockPosition_same
    (r k : ℕ) (hr : 0 < r) (hk : 0 < k)
    (i : Fin k) (d : Fin r) (q : ℕ)
    (hstay : d.val + q < r) :
    cyclicIndex (r * k) (Nat.mul_pos hr hk)
        (blockPosition r k i d) q =
      blockPosition r k i ⟨d.val + q, hstay⟩ := by
  apply Fin.ext
  simp only [cyclicIndex_val, blockPosition_val]
  have hik : i.val + 1 ≤ k := by omega
  have hmul := Nat.mul_le_mul_left r hik
  have hmul' : r * i.val + r ≤ r * k := by
    simpa [Nat.mul_add] using hmul
  have hlt : d.val + r * i.val + q < r * k := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

/--
A cyclic shift by less than one block that crosses the block boundary lands
at the corresponding offset of the next cyclic block.
-/
theorem cyclicIndex_blockPosition_next
    (r k : ℕ) (hr : 0 < r) (hk : 0 < k)
    (i : Fin k) (d : Fin r) (q : ℕ)
    (hq : q < r)
    (hcross : r ≤ d.val + q) :
    cyclicIndex (r * k) (Nat.mul_pos hr hk)
        (blockPosition r k i d) q =
      blockPosition r k (cyclicIndex k hk i 1)
        ⟨d.val + q - r, by omega⟩ := by
  apply Fin.ext
  simp only [cyclicIndex_val, blockPosition_val]
  have hsumlt : d.val + q < 2 * r := by omega
  by_cases hi : i.val + 1 < k
  · have hik : i.val + 2 ≤ k := by omega
    have hmul := Nat.mul_le_mul_left r hik
    have hmul' : r * i.val + 2 * r ≤ r * k := by
      calc
        r * i.val + 2 * r = r * (i.val + 2) := by ring
        _ ≤ r * k := hmul
    have hlt : d.val + r * i.val + q < r * k := by omega
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hi]
    have hnextmul : r * (i.val + 1) = r * i.val + r := by ring
    rw [hnextmul]
    omega
  · have hieq : i.val + 1 = k := by omega
    have hbase : r * k = r * i.val + r := by
      calc
        r * k = r * (i.val + 1) := by rw [hieq]
        _ = r * i.val + r := by ring
    have hoff : d.val + q - r < r := by omega
    have hkone : 1 ≤ k := by omega
    have hrle : r ≤ r * k := by
      simpa using Nat.mul_le_mul_left r hkone
    have hoffTotal : d.val + q - r < r * k := by omega
    have hwrap : (i.val + 1) % k = 0 := by
      rw [hieq, Nat.mod_self]
    have hnum :
        d.val + r * i.val + q = r * k + (d.val + q - r) := by
      omega
    rw [hwrap, Nat.mul_zero, add_zero, hnum]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hoffTotal]

/--
Split each block of length `s+t` into an `s`-slot left segment followed by a
`t`-slot right segment, preserving block order on both sides.
-/
def balancedBlockIndexEquiv (s t k : ℕ) :
    Fin ((s + t) * k) ≃ Fin (s * k) ⊕ Fin (t * k) :=
  (blockPositionEquiv (s + t) k).symm |>.trans
    ((Equiv.prodCongr (Equiv.refl (Fin k)) finSumFinEquiv.symm).trans
      ((Equiv.prodSumDistrib (Fin k) (Fin s) (Fin t)).trans
        (Equiv.sumCongr (blockPositionEquiv s k)
          (blockPositionEquiv t k))))

@[simp] theorem balancedBlockIndexEquiv_left
    (s t k : ℕ) (i : Fin k) (j : Fin s) :
    balancedBlockIndexEquiv s t k
        (blockPosition (s + t) k i (Fin.castAdd t j)) =
      Sum.inl (blockPosition s k i j) := by
  simp [balancedBlockIndexEquiv, blockPosition, blockPositionEquiv]

@[simp] theorem balancedBlockIndexEquiv_right
    (s t k : ℕ) (i : Fin k) (j : Fin t) :
    balancedBlockIndexEquiv s t k
        (blockPosition (s + t) k i (Fin.natAdd s j)) =
      Sum.inr (blockPosition t k i j) := by
  simp [balancedBlockIndexEquiv, blockPosition, blockPositionEquiv]

/--
Interleave two disjoint cyclic enumerations in repeated blocks consisting of
`s` left entries followed by `t` right entries.
-/
def balancedBlockOrder
    {P Q : Set α} {s t k : ℕ}
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q) :
    Fin ((s + t) * k) ≃ (P ∪ Q : Set α) := by
  classical
  exact
    (balancedBlockIndexEquiv s t k).trans
      ((Equiv.sumCongr left right).trans (Equiv.Set.union hPQ).symm)

@[simp] theorem balancedBlockOrder_left
    {P Q : Set α} {s t k : ℕ}
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (i : Fin k) (j : Fin s) :
    ((balancedBlockOrder hPQ left right
        (blockPosition (s + t) k i (Fin.castAdd t j)) :
          (P ∪ Q : Set α)) : α) =
      (left (blockPosition s k i j) : α) := by
  simp [balancedBlockOrder]

@[simp] theorem balancedBlockOrder_right
    {P Q : Set α} {s t k : ℕ}
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (i : Fin k) (j : Fin t) :
    ((balancedBlockOrder hPQ left right
        (blockPosition (s + t) k i (Fin.natAdd s j)) :
          (P ∪ Q : Set α)) : α) =
      (right (blockPosition t k i j) : α) := by
  simp [balancedBlockOrder]

end

end HigherRankKUM
