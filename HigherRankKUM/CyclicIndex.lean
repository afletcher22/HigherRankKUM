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

/-- Cyclic translation by a fixed offset is injective. -/
theorem cyclicIndex_injective_start
    (n : ℕ) (hn : 0 < n) (a : ℕ) :
    Function.Injective (fun i : Fin n => cyclicIndex n hn i a) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  simp only [cyclicIndex_val] at hv
  omega

/-- Offsets smaller than the cycle length are represented injectively. -/
theorem cyclicIndex_injective_offsets
    (n : ℕ) (hn : 0 < n) (i : Fin n) :
    Function.Injective (fun t : Fin n => cyclicIndex n hn i t.val) := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  simp only [cyclicIndex_val] at hv
  omega

/-- Every cyclic position has a unique relative offset from a fixed start. -/
theorem existsUnique_cyclicIndex_offset
    (n : ℕ) (hn : 0 < n) (i q : Fin n) :
    ∃! t : Fin n, q = cyclicIndex n hn i t.val := by
  let t : Fin n := ⟨(q.val + n - i.val) % n, Nat.mod_lt _ hn⟩
  have ht : q = cyclicIndex n hn i t.val := by
    apply Fin.ext
    simp only [cyclicIndex_val]
    dsimp [t]
    omega
  refine ⟨t, ht, ?_⟩
  intro u hu
  exact cyclicIndex_injective_offsets n hn i (hu.symm.trans ht)

end

end HigherRankKUM
