import HigherRankKUM.Rank4.FourBlockPerm

namespace HigherRankKUM
namespace Rank4FourBlockMove

open Set

noncomputable section

variable {α : Type*}

/-- Elementary modular arithmetic behind four-block support.

If `t < n`, `a,b < 4`, and `t+a = b (mod n)`, then `t` is within
three positions of one of the two ends of the standard interval
`0,...,n-1`. -/
theorem offset_le_three_or_ge_sub_three_of_mod_eq
    {n t a b : ℕ}
    (h7n : 7 ≤ n)
    (ht : t < n)
    (ha : a < 4)
    (hb : b < 4)
    (hmod : (t + a) % n = b) :
    t ≤ 3 ∨ n - 3 ≤ t := by
  by_cases hlt : t + a < n
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    left
    omega
  · have hge : n ≤ t + a := by omega
    have h2n : t + a < 2 * n := by omega
    have hsub : t + a - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub] at hmod
    right
    omega

/-- The six possible noncentral starts of rank-four windows meeting a moved
four-position block. -/
def fourBlockBoundaryStarts
    {n : ℕ} (hn : 0 < n) (s : Fin n) : Set (Fin n) :=
  ({cyclicIndex n hn s (n - 3),
    cyclicIndex n hn s (n - 2),
    cyclicIndex n hn s (n - 1),
    cyclicIndex n hn s 1,
    cyclicIndex n hn s 2,
    cyclicIndex n hn s 3} : Set (Fin n))

/-- Any noncentral rank-four position window that overlaps the moved
four-position block starts at one of the six boundary offsets
`s-3,s-2,s-1,s+1,s+2,s+3`. -/
theorem mem_fourBlockBoundaryStarts_of_overlap
    {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    {s i : Fin n}
    (his : i ≠ s)
    (hover :
      ¬ Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s)) :
    i ∈ fourBlockBoundaryStarts hn s := by
  obtain ⟨p, hpi, hps⟩ := Set.not_disjoint_iff.mp hover
  rcases hpi with ⟨q, hq⟩
  rcases hps with ⟨r, hr⟩
  have hidx :
      cyclicIndex n hn i q.val = cyclicIndex n hn s r.val :=
    hq.trans hr.symm
  obtain ⟨t, ht, -⟩ := existsUnique_cyclicIndex_offset n hn s i
  rw [ht, cyclicIndex_add] at hidx
  have hmodEq : t.val + q.val ≡ r.val [MOD n] := by
    apply Nat.ModEq.add_left_cancel' s.val
    change
      (s.val + (t.val + q.val)) % n =
        (s.val + r.val) % n
    exact congrArg Fin.val hidx
  have hmod : (t.val + q.val) % n = r.val := by
    change (t.val + q.val) % n = r.val % n at hmodEq
    simpa [Nat.mod_eq_of_lt r.isLt] using hmodEq
  have hnear :=
    offset_le_three_or_ge_sub_three_of_mod_eq
      h7n t.isLt q.isLt r.isLt hmod
  rcases hnear with hlow | hhigh
  · have hcases :
        t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3
    · exfalso
      apply his
      simpa [h0, cyclicIndex_zero] using ht
    · simp [fourBlockBoundaryStarts, ht, h1]
    · simp [fourBlockBoundaryStarts, ht, h2]
    · simp [fourBlockBoundaryStarts, ht, h3]
  · have hcases :
        t.val = n - 3 ∨ t.val = n - 2 ∨ t.val = n - 1 := by
      omega
    rcases hcases with hm3 | hm2 | hm1
    · simp [fourBlockBoundaryStarts, ht, hm3]
    · simp [fourBlockBoundaryStarts, ht, hm2]
    · simp [fourBlockBoundaryStarts, ht, hm1]

/-- Conversely, a noncentral start outside the six boundary offsets has a
rank-four position window disjoint from the moved block. -/
theorem disjoint_fourBlockPositions_of_notMem_boundary
    {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    {s i : Fin n}
    (his : i ≠ s)
    (hi : i ∉ fourBlockBoundaryStarts hn s) :
    Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s) := by
  by_contra hover
  exact hi (mem_fourBlockBoundaryStarts_of_overlap hn h7n his hover)

/-- Exact six-window certification theorem for a four-block reorder.

For cycles of length at least seven, the central moved window is automatically
a base and all remote windows are unchanged.  Thus only the six boundary
starts `s±1,s±2,s±3` need to be checked. -/
theorem cyclicBasisOrder_of_fourBlockReorder_of_six_boundary_bases
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    {σ τ : Fin n ≃ E} {s : Fin n}
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hmove : FourBlockReorder hn σ τ s)
    (hm3 : M.IsBase
      (cyclicWindow 4 hn τ (cyclicIndex n hn s (n - 3))))
    (hm2 : M.IsBase
      (cyclicWindow 4 hn τ (cyclicIndex n hn s (n - 2))))
    (hm1 : M.IsBase
      (cyclicWindow 4 hn τ (cyclicIndex n hn s (n - 1))))
    (hp1 : M.IsBase
      (cyclicWindow 4 hn τ (cyclicIndex n hn s 1)))
    (hp2 : M.IsBase
      (cyclicWindow 4 hn τ (cyclicIndex n hn s 2)))
    (hp3 : M.IsBase
      (cyclicWindow 4 hn τ (cyclicIndex n hn s 3))) :
    CyclicBasisOrder M 4 hn τ := by
  apply cyclicBasisOrder_of_fourBlockReorder_of_boundary_bases hσ hmove
  intro i his hover
  have hi :=
    mem_fourBlockBoundaryStarts_of_overlap hn h7n his hover
  simp only [fourBlockBoundaryStarts, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hi
  rcases hi with hi | hi | hi | hi | hi | hi
  · simpa [hi] using hm3
  · simpa [hi] using hm2
  · simpa [hi] using hm1
  · simpa [hi] using hp1
  · simpa [hi] using hp2
  · simpa [hi] using hp3

/-- Explicit-permutation version of the six-window certification theorem. -/
theorem cyclicBasisOrder_applyFourBlockPerm_of_six_boundary_bases
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4))
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hm3 : M.IsBase
      (cyclicWindow 4 hn (applyFourBlockPerm hn (by omega) σ s π)
        (cyclicIndex n hn s (n - 3))))
    (hm2 : M.IsBase
      (cyclicWindow 4 hn (applyFourBlockPerm hn (by omega) σ s π)
        (cyclicIndex n hn s (n - 2))))
    (hm1 : M.IsBase
      (cyclicWindow 4 hn (applyFourBlockPerm hn (by omega) σ s π)
        (cyclicIndex n hn s (n - 1))))
    (hp1 : M.IsBase
      (cyclicWindow 4 hn (applyFourBlockPerm hn (by omega) σ s π)
        (cyclicIndex n hn s 1)))
    (hp2 : M.IsBase
      (cyclicWindow 4 hn (applyFourBlockPerm hn (by omega) σ s π)
        (cyclicIndex n hn s 2)))
    (hp3 : M.IsBase
      (cyclicWindow 4 hn (applyFourBlockPerm hn (by omega) σ s π)
        (cyclicIndex n hn s 3))) :
    CyclicBasisOrder M 4 hn
      (applyFourBlockPerm hn (by omega) σ s π) := by
  exact cyclicBasisOrder_of_fourBlockReorder_of_six_boundary_bases
    hn h7n hσ
    (fourBlockReorder_applyFourBlockPerm hn (by omega) σ s π)
    hm3 hm2 hm1 hp1 hp2 hp3

end

end Rank4FourBlockMove
end HigherRankKUM
