import HigherRankKUM.BlockerClosure
import HigherRankKUM.Rank4.CyclicWindowFour

namespace HigherRankKUM
namespace Rank4BlockerCycle

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- A blocker at cyclic start `i`: the omitted element `e` lies in the
closure of the three consecutive entries beginning at `i`. -/
def blockerAt
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (e : α) (i : Fin n) : Prop :=
  e ∈ M.closure (cyclicWindow 3 hn σ i)

/-- Two successive length-three windows together are exactly the corresponding
length-four window. -/
theorem cyclicWindow_three_union_next_eq_four
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow 3 hn σ i ∪
        cyclicWindow 3 hn σ (cyclicIndex n hn i 1) =
      cyclicWindow 4 hn σ i := by
  rw [cyclicWindow_three_eq, cyclicWindow_three_eq, cyclicWindow_four_eq]
  simp only [cyclicIndex_add]
  simp [Nat.add_assoc]

/-- In a cycle of length at least six, a length-three window is disjoint from
the length-three window starting three steps later. -/
theorem cyclicWindow_three_disjoint_shift_three
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h6n : 6 ≤ n)
    (σ : Fin n ≃ E) (i : Fin n) :
    Disjoint (cyclicWindow 3 hn σ i)
      (cyclicWindow 3 hn σ (cyclicIndex n hn i 3)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [cyclicWindow, Set.mem_range] at hx hy
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  have hidx :
      cyclicIndex n hn i a.val =
        cyclicIndex n hn (cyclicIndex n hn i 3) b.val := by
    apply σ.injective
    apply Subtype.ext
    exact ha.trans hb.symm
  rw [cyclicIndex_add] at hidx
  have haN : a.val < n := by omega
  have hbN : 3 + b.val < n := by omega
  have hab :
      a.val = 3 + b.val :=
    cyclicIndex_injective_offsets n hn i haN hbN hidx
  omega

/-- The four successive blocker triples have empty common intersection when
the cycle has length at least six. -/
theorem four_successive_triples_inter_empty
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h6n : 6 ≤ n)
    (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow 3 hn σ i ∩
        cyclicWindow 3 hn σ (cyclicIndex n hn i 1) ∩
        cyclicWindow 3 hn σ (cyclicIndex n hn i 2) ∩
        cyclicWindow 3 hn σ (cyclicIndex n hn i 3) = ∅ := by
  have hdis :=
    cyclicWindow_three_disjoint_shift_three hn h6n σ i
  rw [Set.disjoint_left] at hdis
  ext x
  simp only [Set.mem_inter_iff, Set.not_mem_empty, iff_false]
  intro hx
  exact hdis hx.1.1.1 hx.2

/-- Four consecutive blockers are impossible along a rank-four cyclic basis
ordering.

This is the formal cyclic version of the closure-intersection observation:
successive blocker triples overlap inside basis windows, so four blockers
would force the nonloop `e` into the closure of an empty common
intersection. -/
theorem no_four_consecutive_blockers
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h6n : 6 ≤ n)
    (σ : Fin n ≃ E) (e : α)
    (he : M.IsNonloop e)
    (hCBO : CyclicBasisOrder M 4 hn σ)
    (i : Fin n) :
    ¬ (blockerAt M hn σ e i ∧
       blockerAt M hn σ e (cyclicIndex n hn i 1) ∧
       blockerAt M hn σ e (cyclicIndex n hn i 2) ∧
       blockerAt M hn σ e (cyclicIndex n hn i 3)) := by
  let W := cyclicWindow 3 hn σ i
  let X := cyclicWindow 3 hn σ (cyclicIndex n hn i 1)
  let Y := cyclicWindow 3 hn σ (cyclicIndex n hn i 2)
  let Z := cyclicWindow 3 hn σ (cyclicIndex n hn i 3)

  have hWX : M.Indep (W ∪ X) := by
    have hbase := hCBO i
    rw [← cyclicWindow_three_union_next_eq_four hn σ i] at hbase
    simpa [W, X] using hbase.indep

  have hXY : M.Indep (X ∪ Y) := by
    let i1 := cyclicIndex n hn i 1
    have hbase := hCBO i1
    rw [← cyclicWindow_three_union_next_eq_four hn σ i1] at hbase
    have h2 :
        cyclicIndex n hn i1 1 = cyclicIndex n hn i 2 := by
      simp [i1, cyclicIndex_add]
    simpa [X, Y, i1, h2] using hbase.indep

  have hYZ : M.Indep (Y ∪ Z) := by
    let i2 := cyclicIndex n hn i 2
    have hbase := hCBO i2
    rw [← cyclicWindow_three_union_next_eq_four hn σ i2] at hbase
    have h3 :
        cyclicIndex n hn i2 1 = cyclicIndex n hn i 3 := by
      simp [i2, cyclicIndex_add]
    simpa [Y, Z, i2, h3] using hbase.indep

  have hEmpty : W ∩ X ∩ Y ∩ Z = ∅ := by
    simpa [W, X, Y, Z] using
      four_successive_triples_inter_empty hn h6n σ i

  intro hblocks
  apply BlockerClosure.not_four_closures_of_nonloop_of_fourfold_inter_empty
      he hWX hXY hYZ hEmpty
  simpa [blockerAt, W, X, Y, Z] using hblocks

end

end Rank4BlockerCycle
end HigherRankKUM
