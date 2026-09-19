import Mathlib.Tactic

namespace HigherRankKUM

noncomputable section

/-- Add a natural offset to a finite cyclic index. -/
def cyclicIndex (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ) : Fin n :=
  ⟨(i.val + j) % n, Nat.mod_lt _ hn⟩

@[simp] theorem cyclicIndex_val
    (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ) :
    (cyclicIndex n hn i j).val = (i.val + j) % n := by
  rfl

@[simp] theorem cyclicIndex_zero
    (n : ℕ) (hn : 0 < n) (i : Fin n) :
    cyclicIndex n hn i 0 = i := by
  apply Fin.ext
  simp [cyclicIndex, Nat.mod_eq_of_lt i.isLt]

/-- Successive cyclic shifts compose by adding their offsets. -/
theorem cyclicIndex_add
    (n : ℕ) (hn : 0 < n) (i : Fin n) (a b : ℕ) :
    cyclicIndex n hn (cyclicIndex n hn i a) b =
      cyclicIndex n hn i (a + b) := by
  apply Fin.ext
  simp only [cyclicIndex_val]
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Every cyclic position has a relative offset from a fixed start. -/
theorem exists_cyclicIndex_offset
    (n : ℕ) (hn : 0 < n) (i q : Fin n) :
    ∃ t : Fin n, q = cyclicIndex n hn i t.val := by
  let t : Fin n := ⟨(q.val + n - i.val) % n, Nat.mod_lt _ hn⟩
  refine ⟨t, ?_⟩
  apply Fin.ext
  simp only [cyclicIndex_val]
  dsimp [t]
  simp only [Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]
  have hsum : i.val + (q.val + n - i.val) = q.val + n := by omega
  rw [← Nat.add_mod, hsum, Nat.add_mod]
  simp [Nat.mod_eq_of_lt q.isLt]

end

end HigherRankKUM
