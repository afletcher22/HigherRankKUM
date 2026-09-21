import HigherRankKUM.Rank4.BlockerCycle

namespace HigherRankKUM
namespace Rank4BlockerRuns

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- Distinct cyclic offsets below the cycle length give distinct ground
elements under a cyclic enumeration. -/
theorem order_value_ne_of_offset_ne
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (i : Fin n)
    {a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (σ (cyclicIndex n hn i a) : α) ≠
      (σ (cyclicIndex n hn i b) : α) := by
  intro h
  apply hab
  apply cyclicIndex_injective_offsets n hn i ha hb
  apply σ.injective
  apply Subtype.ext
  exact h

/-- Two successive length-three cyclic windows intersect in exactly their
shared length-two window. -/
theorem cyclicWindow_three_inter_shift_one_eq_two
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow 3 hn σ i ∩
        cyclicWindow 3 hn σ (cyclicIndex n hn i 1) =
      cyclicWindow 2 hn σ (cyclicIndex n hn i 1) := by
  let i1 := cyclicIndex n hn i 1
  let i2 := cyclicIndex n hn i 2
  let i3 := cyclicIndex n hn i 3
  have h01 :
      (σ i : α) ≠ (σ i1 : α) := by
    simpa [i1] using
      (order_value_ne_of_offset_ne hn σ i
        (a := 0) (b := 1) (by omega) (by omega) (by omega))
  have h02 :
      (σ i : α) ≠ (σ i2 : α) := by
    simpa [i2] using
      (order_value_ne_of_offset_ne hn σ i
        (a := 0) (b := 2) (by omega) (by omega) (by omega))
  have h03 :
      (σ i : α) ≠ (σ i3 : α) := by
    simpa [i3] using
      (order_value_ne_of_offset_ne hn σ i
        (a := 0) (b := 3) (by omega) (by omega) (by omega))
  rw [cyclicWindow_three_eq, cyclicWindow_three_eq, cyclicWindow_two_eq]
  simp only [cyclicIndex_add]
  change
    ({(σ i : α), (σ i1 : α), (σ i2 : α)} : Set α) ∩
        ({(σ i1 : α), (σ i2 : α), (σ i3 : α)} : Set α) =
      ({(σ i1 : α), (σ i2 : α)} : Set α)
  ext x
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx0 | hx1 | hx2, hy1 | hy2 | hy3⟩
    · subst x
      exact (h01 hy1).elim
    · subst x
      exact (h02 hy2).elim
    · subst x
      exact (h03 hy3).elim
    · exact Or.inl hx1
    · exact Or.inl hx1
    · exact Or.inl hx1
    · exact Or.inr hx2
    · exact Or.inr hx2
    · exact Or.inr hx2
  · intro hx
    rcases hx with hx | hx
    · subst x
      exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩
    · subst x
      exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩

/-- Length-three windows whose starts differ by two positions intersect in
exactly the single middle element. -/
theorem cyclicWindow_three_inter_shift_two_eq_singleton
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h5n : 5 ≤ n)
    (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow 3 hn σ i ∩
        cyclicWindow 3 hn σ (cyclicIndex n hn i 2) =
      ({(σ (cyclicIndex n hn i 2) : α)} : Set α) := by
  let i2 := cyclicIndex n hn i 2
  let i3 := cyclicIndex n hn i 3
  let i4 := cyclicIndex n hn i 4
  have h02 :
      (σ i : α) ≠ (σ i2 : α) := by
    simpa [i2] using
      (order_value_ne_of_offset_ne hn σ i
        (a := 0) (b := 2) (by omega) (by omega) (by omega))
  have h03 :
      (σ i : α) ≠ (σ i3 : α) := by
    simpa [i3] using
      (order_value_ne_of_offset_ne hn σ i
        (a := 0) (b := 3) (by omega) (by omega) (by omega))
  have h04 :
      (σ i : α) ≠ (σ i4 : α) := by
    simpa [i4] using
      (order_value_ne_of_offset_ne hn σ i
        (a := 0) (b := 4) (by omega) (by omega) (by omega))
  have h12 :
      (σ (cyclicIndex n hn i 1) : α) ≠ (σ i2 : α) := by
    simpa [i2] using
      (order_value_ne_of_offset_ne hn σ i
        (a := 1) (b := 2) (by omega) (by omega) (by omega))
  have h13 :
      (σ (cyclicIndex n hn i 1) : α) ≠ (σ i3 : α) := by
    simpa [i3] using
      (order_value_ne_of_offset_ne hn σ i
        (a := 1) (b := 3) (by omega) (by omega) (by omega))
  have h14 :
      (σ (cyclicIndex n hn i 1) : α) ≠ (σ i4 : α) := by
    simpa [i4] using
      (order_value_ne_of_offset_ne hn σ i
        (a := 1) (b := 4) (by omega) (by omega) (by omega))
  rw [cyclicWindow_three_eq, cyclicWindow_three_eq]
  simp only [cyclicIndex_add]
  change
    ({(σ i : α),
      (σ (cyclicIndex n hn i 1) : α),
      (σ i2 : α)} : Set α) ∩
        ({(σ i2 : α), (σ i3 : α), (σ i4 : α)} : Set α) =
      ({(σ i2 : α)} : Set α)
  ext x
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx0 | hx1 | hx2, hy2 | hy3 | hy4⟩
    · subst x
      exact (h02 hy2).elim
    · subst x
      exact (h03 hy3).elim
    · subst x
      exact (h04 hy4).elim
    · subst x
      exact (h12 hy2).elim
    · subst x
      exact (h13 hy3).elim
    · subst x
      exact (h14 hy4).elim
    · exact hx2
    · exact hx2
    · exact hx2
  · intro hx
    subst x
    exact ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩

/-- Two consecutive blockers force the omitted element into the closure of
their shared pair. -/
theorem two_consecutive_blockers_mem_closure_shared_pair
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (e : α)
    (hCBO : CyclicBasisOrder M 4 hn σ)
    (i : Fin n)
    (h0 : Rank4BlockerCycle.blockerAt M hn σ e i)
    (h1 : Rank4BlockerCycle.blockerAt M hn σ e
      (cyclicIndex n hn i 1)) :
    e ∈ M.closure
      (cyclicWindow 2 hn σ (cyclicIndex n hn i 1)) := by
  let W := cyclicWindow 3 hn σ i
  let X := cyclicWindow 3 hn σ (cyclicIndex n hn i 1)
  have hInd : M.Indep (W ∪ X) := by
    have hbase := hCBO i
    rw [← Rank4BlockerCycle.cyclicWindow_three_union_next_eq_four hn σ i] at hbase
    simpa [W, X] using hbase.indep
  have hmem : e ∈ M.closure (W ∩ X) :=
    BlockerClosure.mem_closure_inter_of_indep_union hInd h0 h1
  have hEq :
      W ∩ X =
        cyclicWindow 2 hn σ (cyclicIndex n hn i 1) := by
    simpa [W, X] using
      cyclicWindow_three_inter_shift_one_eq_two hn h4n σ i
  rwa [hEq] at hmem

/-- Three consecutive blockers force the omitted element into the closure of
the single element common to all three blocker triples.

This is the formal source of the “parallel obstruction” interpretation of a
three-run in the blocker word. -/
theorem three_consecutive_blockers_mem_closure_shared_singleton
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h5n : 5 ≤ n)
    (σ : Fin n ≃ E) (e : α)
    (hCBO : CyclicBasisOrder M 4 hn σ)
    (i : Fin n)
    (h0 : Rank4BlockerCycle.blockerAt M hn σ e i)
    (h1 : Rank4BlockerCycle.blockerAt M hn σ e
      (cyclicIndex n hn i 1))
    (h2 : Rank4BlockerCycle.blockerAt M hn σ e
      (cyclicIndex n hn i 2)) :
    e ∈ M.closure
      ({(σ (cyclicIndex n hn i 2) : α)} : Set α) := by
  let W := cyclicWindow 3 hn σ i
  let X := cyclicWindow 3 hn σ (cyclicIndex n hn i 1)
  let Y := cyclicWindow 3 hn σ (cyclicIndex n hn i 2)

  have hWX : M.Indep (W ∪ X) := by
    have hbase := hCBO i
    rw [← Rank4BlockerCycle.cyclicWindow_three_union_next_eq_four hn σ i] at hbase
    simpa [W, X] using hbase.indep

  have hXY : M.Indep (X ∪ Y) := by
    let i1 := cyclicIndex n hn i 1
    have hbase := hCBO i1
    rw [← Rank4BlockerCycle.cyclicWindow_three_union_next_eq_four hn σ i1] at hbase
    have h2idx :
        cyclicIndex n hn i1 1 = cyclicIndex n hn i 2 := by
      simp [i1, cyclicIndex_add]
    simpa [X, Y, i1, h2idx] using hbase.indep

  have hmem : e ∈ M.closure (W ∩ X ∩ Y) :=
    BlockerClosure.mem_closure_triple_inter_of_adjacent_indep
      hWX hXY h0 h1 h2

  have hWY :
      W ∩ Y =
        ({(σ (cyclicIndex n hn i 2) : α)} : Set α) := by
    simpa [W, Y] using
      cyclicWindow_three_inter_shift_two_eq_singleton hn h5n σ i

  have hEq :
      W ∩ X ∩ Y =
        ({(σ (cyclicIndex n hn i 2) : α)} : Set α) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxWY : x ∈ W ∩ Y := ⟨hx.1.1, hx.2⟩
      rw [hWY] at hxWY
      exact hxWY
    · intro x hx
      have hxval :
          x = (σ (cyclicIndex n hn i 2) : α) := by
        simpa using hx
      subst x
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · dsimp [W]
        rw [cyclicWindow_three_eq]
        exact Or.inr (Or.inr rfl)
      · dsimp [X]
        rw [cyclicWindow_three_eq]
        simp [cyclicIndex_add]
      · dsimp [Y]
        rw [cyclicWindow_three_eq]
        simp [cyclicIndex_zero]

  rwa [hEq] at hmem

end

end Rank4BlockerRuns
end HigherRankKUM
