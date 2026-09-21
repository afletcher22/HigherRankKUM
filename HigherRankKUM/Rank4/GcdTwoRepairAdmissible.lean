import HigherRankKUM.Rank4.GcdTwoRepairTransition

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open PairCycleIndexing

variable {α : Type*}

/-- For `h=2`, an aligned window is exactly the union of a pair block and the
next cyclic pair block.  This statement is independent of any matroid basis
hypotheses and applies to an arbitrary pair equivalence. -/
theorem alignedWindow_two_eq_pairSet_union_next
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (e : Fin N × Bool ≃ M.E) (t : Fin N) :
    AdmissiblePairCycle.alignedWindow (h := 2) hN e t =
      AdmissiblePairCycle.pairSet e t ∪
        AdmissiblePairCycle.pairSet e (cyclicIndex N hN t 1) := by
  ext x
  constructor
  · rintro ⟨⟨k, b⟩, rfl⟩
    fin_cases k <;> cases b <;>
      simp [AdmissiblePairCycle.alignedWindow, AdmissiblePairCycle.pairSet,
        AdmissiblePairCycle.elem]
  · intro hx
    simp only [AdmissiblePairCycle.pairSet, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (h | h) | (h | h)
    · subst x
      exact ⟨(⟨0, by omega⟩, false), by
        simp [AdmissiblePairCycle.alignedWindow, AdmissiblePairCycle.elem]⟩
    · subst x
      exact ⟨(⟨0, by omega⟩, true), by
        simp [AdmissiblePairCycle.alignedWindow, AdmissiblePairCycle.elem]⟩
    · subst x
      exact ⟨(⟨1, by omega⟩, false), rfl⟩
    · subst x
      exact ⟨(⟨1, by omega⟩, true), rfl⟩

/-- A legal local rank-four repartition produces a new admissible pair cycle on
the same matroid.  Thus the abstract common-base repair is now a genuine state
transition in the pair-cycle search space, rather than merely a local set
replacement.

The only windows needing new basis proofs are the left boundary, the middle
window containing both replaced blocks, and the right boundary. -/
noncomputable def repairedAdmissiblePairCycle
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (R : LocalRepartition A s) :
    AdmissiblePairCycle.Data M N 2 hN where
  pairEquiv := repairedPairEquiv A h2N s R
  groundSize := A.groundSize
  rankEq := A.rankEq
  alignedBase := by
    intro t
    rw [alignedWindow_two_eq_pairSet_union_next]
    let c := cyclicIndex N hN s 1
    let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
    let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
    have hci_next : cyclicIndex N hN c 1 = i := by
      simp [c, i, AdjacentRepair.leftBoundaryIndex, cyclicIndex_add]
    have hij_next : cyclicIndex N hN i 1 = j := by
      simpa [i, j] using
        (rightBoundaryIndex_eq_next_leftBoundaryIndex (N := N) (hN := hN) s).symm
    have hci : c ≠ i := by
      rw [← hci_next]
      exact (cyclicIndex_ne_self_of_pos_of_lt N hN c (by omega) (by omega)).symm
    have hcj : c ≠ j := by
      have hjc : j = cyclicIndex N hN c 2 := by
        simpa [c, j] using
          rightBoundaryIndex_eq_two_after_core_block (N := N) (hN := hN) s
      rw [hjc]
      exact (cyclicIndex_ne_self_of_pos_of_lt N hN c (by omega) h2N).symm
    have hij : i ≠ j := modified_indices_ne h2N s
    by_cases htc : t = c
    · subst t
      rw [repairedPairEquiv_other_pairSet A h2N s R c hci hcj]
      rw [hci_next]
      rw [repairedPairEquiv_left_pairSet A h2N s R]
      have hbase := R.leftBoundaryBase
      rw [core_eq_next_block A s] at hbase
      simpa [c, Set.union_comm] using hbase
    by_cases hti : t = i
    · subst t
      rw [repairedPairEquiv_left_pairSet A h2N s R]
      rw [hij_next]
      rw [repairedPairEquiv_right_pairSet A h2N s R]
      rw [R.union_eq]
      have hold := A.alignedBase i
      rw [alignedWindow_two_eq_pairSet_union_next] at hold
      rw [hij_next] at hold
      simpa [repairGround, i, j] using hold
    by_cases htj : t = j
    · subst t
      rw [repairedPairEquiv_right_pairSet A h2N s R]
      have hnextj_ne_j : cyclicIndex N hN j 1 ≠ j :=
        cyclicIndex_ne_self_of_pos_of_lt N hN j (by omega) (by omega)
      have hnextj_eq_i2 : cyclicIndex N hN j 1 = cyclicIndex N hN i 2 := by
        rw [← hij_next, cyclicIndex_add]
      have hnextj_ne_i : cyclicIndex N hN j 1 ≠ i := by
        rw [hnextj_eq_i2]
        exact cyclicIndex_ne_self_of_pos_of_lt N hN i (by omega) h2N
      rw [repairedPairEquiv_other_pairSet A h2N s R
        (cyclicIndex N hN j 1) hnextj_ne_i hnextj_ne_j]
      have hbase := R.rightBoundaryBase
      rw [core_eq_next_block A j] at hbase
      simpa [j] using hbase
    · have hnext_ne_i : cyclicIndex N hN t 1 ≠ i := by
        intro hEq
        apply htc
        apply cyclicIndex_injective_start N hN 1
        calc
          cyclicIndex N hN t 1 = i := hEq
          _ = cyclicIndex N hN c 1 := hci_next.symm
      have hnext_ne_j : cyclicIndex N hN t 1 ≠ j := by
        intro hEq
        apply hti
        apply cyclicIndex_injective_start N hN 1
        calc
          cyclicIndex N hN t 1 = j := hEq
          _ = cyclicIndex N hN i 1 := hij_next.symm
      rw [repairedPairEquiv_other_pairSet A h2N s R t hti htj]
      rw [repairedPairEquiv_other_pairSet A h2N s R
        (cyclicIndex N hN t 1) hnext_ne_i hnext_ne_j]
      have hold := A.alignedBase t
      rw [alignedWindow_two_eq_pairSet_union_next] at hold
      exact hold

end Rank4GcdTwoRepair
end HigherRankKUM
