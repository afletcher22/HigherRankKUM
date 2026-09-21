import HigherRankKUM.CyclicIndex

namespace HigherRankKUM

noncomputable section

/-- If an offset does not reach the end of the cycle, `cyclicIndex` is
ordinary addition. -/
theorem cyclicIndex_eq_mk_add_of_lt
    (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ)
    (h : i.val + j < n) :
    cyclicIndex n hn i j = ⟨i.val + j, h⟩ := by
  apply Fin.ext
  simp [cyclicIndex, Nat.mod_eq_of_lt h]

/-- If an offset crosses the end exactly once, `cyclicIndex` is subtraction
of one cycle length.  This is the only wrap case needed for rank-four
length-four windows in the direct dangerous-branch schedules. -/
theorem cyclicIndex_eq_mk_sub_of_ge_of_lt_two_mul
    (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ)
    (hge : n ≤ i.val + j)
    (hlt : i.val + j < 2 * n) :
    cyclicIndex n hn i j =
      ⟨i.val + j - n, by omega⟩ := by
  apply Fin.ext
  simp only [cyclicIndex_val, Fin.val_mk]
  rw [Nat.mod_eq_sub_mod hge]
  rw [Nat.mod_eq_of_lt (by omega)]

end

end HigherRankKUM
