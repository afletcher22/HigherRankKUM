import HigherRankKUM.LocalRepairClosure
import HigherRankKUM.AdjacentRepair

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open Set
open PairCycleIndexing

variable {α : Type*}

/-- In rank four (`h=2`), the shifted-window core consists of exactly the next
pair block. -/
theorem core_eq_next_block
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) :
    A.core s = A.block (cyclicIndex N hN s 1) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rcases z with ⟨z, b⟩
    have hz : z = 0 := Fin.eq_zero z
    subst z
    cases b <;> simp [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet]
  · intro hx
    simp only [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨(⟨0, by omega⟩, false), ?_⟩
      rfl
    · refine ⟨(⟨0, by omega⟩, true), ?_⟩
      rfl

/-- For `h=2`, the right modified pair is two cyclic steps after the unique
block making up the left core. -/
theorem rightBoundaryIndex_eq_two_after_core_block
    {N : ℕ} {hN : 0 < N} (s : Fin N) :
    AdjacentRepair.rightBoundaryIndex N 2 hN s =
      cyclicIndex N hN (cyclicIndex N hN s 1) 2 := by
  symm
  rw [cyclicIndex_add]
  rfl

/-- For `h=2`, the right modified pair is one step after the left modified
pair. -/
theorem rightBoundaryIndex_eq_next_leftBoundaryIndex
    {N : ℕ} {hN : 0 < N} (s : Fin N) :
    AdjacentRepair.rightBoundaryIndex N 2 hN s =
      cyclicIndex N hN (AdjacentRepair.leftBoundaryIndex N 2 hN s) 1 := by
  symm
  rw [AdjacentRepair.leftBoundaryIndex, cyclicIndex_add]
  rfl

/-- The right modified pair is disjoint from the left unchanged core whenever
`2 < N`. -/
theorem right_block_disjoint_left_core
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    Disjoint (A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s)) (A.core s) := by
  rw [core_eq_next_block A s]
  apply A.block_disjoint_of_ne
  intro hEq
  have hEq' : cyclicIndex N hN (cyclicIndex N hN s 1) 2 =
      cyclicIndex N hN s 1 := by
    rw [← rightBoundaryIndex_eq_two_after_core_block s]
    exact hEq
  exact (cyclicIndex_ne_self_of_pos_of_lt N hN (cyclicIndex N hN s 1)
    (by omega) h2N) hEq'

/-- The left modified pair is disjoint from the right unchanged core whenever
`2 < N`. -/
theorem left_block_disjoint_right_core
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    Disjoint (A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s))
      (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s)) := by
  rw [core_eq_next_block A (AdjacentRepair.rightBoundaryIndex N 2 hN s)]
  apply A.block_disjoint_of_ne
  intro hEq
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  have hj : AdjacentRepair.rightBoundaryIndex N 2 hN s = cyclicIndex N hN i 1 := by
    simpa [i] using rightBoundaryIndex_eq_next_leftBoundaryIndex (N := N) (hN := hN) s
  have hnext : cyclicIndex N hN (AdjacentRepair.rightBoundaryIndex N 2 hN s) 1 =
      cyclicIndex N hN i 2 := by
    rw [hj, cyclicIndex_add]
  have hEq' : i = cyclicIndex N hN i 2 := by
    rw [← hnext]
    exact hEq
  exact (cyclicIndex_ne_self_of_pos_of_lt N hN i (by omega) h2N) hEq'.symm

/-- The right modified block lies in the left boundary contraction ground. -/
theorem right_block_subset_left_contract_ground
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s) ⊆
      (M.contract (A.core s)).E := by
  intro e he
  rw [Matroid.contract_ground]
  refine ⟨A.block_subset_ground _ he, ?_⟩
  intro hecore
  exact Set.disjoint_left.1 (right_block_disjoint_left_core A h2N s) he hecore

/-- The left modified block lies in the right boundary contraction ground. -/
theorem left_block_subset_right_contract_ground
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) ⊆
      (M.contract (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s))).E := by
  intro e he
  rw [Matroid.contract_ground]
  refine ⟨A.block_subset_ground _ he, ?_⟩
  intro hecore
  exact Set.disjoint_left.1 (left_block_disjoint_right_core A h2N s) he hecore

end Rank4GcdTwoRepair
end HigherRankKUM
