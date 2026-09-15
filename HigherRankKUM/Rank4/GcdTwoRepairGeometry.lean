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

/-- The four elements involved in the adjacent repair. -/
def repairGround
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) : Set α :=
  A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) ∪
    A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s)

/-- Left rank-two boundary minor controlling an adjacent repair. -/
def leftRepairMinor
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) : Matroid α :=
  LocalRepairClosure.boundaryMinor M (A.core s) (repairGround A s)

/-- Right rank-two boundary minor controlling an adjacent repair. -/
def rightRepairMinor
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) : Matroid α :=
  LocalRepairClosure.boundaryMinor M
    (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s)) (repairGround A s)

/-- The two modified pair blocks are distinct and disjoint. -/
theorem modified_blocks_disjoint
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    Disjoint (A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s))
      (A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s)) := by
  apply A.block_disjoint_of_ne
  rw [rightBoundaryIndex_eq_next_leftBoundaryIndex (N := N) (hN := hN) s]
  exact (cyclicIndex_ne_self_of_pos_of_lt N hN
    (AdjacentRepair.leftBoundaryIndex N 2 hN s) (by omega) (by omega)).symm

/-- The left modified block is a base of the left repair minor. -/
theorem left_block_isBase_leftRepairMinor
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    (leftRepairMinor A s).IsBase
      (A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s)) := by
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  have hdis : Disjoint (A.block i) (A.core s) := by
    simpa [i, AdjacentRepair.leftBoundaryIndex,
      AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      A.endpoint_block_disjoint_core (by omega) h2N s
  have hbase : M.IsBase (A.block i ∪ A.core s) := by
    simpa [i, AdjacentRepair.leftBoundaryIndex] using A.endpoint_basis_right (by omega) s
  have hcontract : (M.contract (A.core s)).IsBase (A.block i) :=
    (A.core_indep (by omega) s).contract_isBase_iff.2 ⟨hbase, hdis⟩
  have hiGround : A.block i ⊆ (M.contract (A.core s)).E :=
    hcontract.subset_ground
  have hjGround : A.block j ⊆ (M.contract (A.core s)).E := by
    simpa [j] using right_block_subset_left_contract_ground A h2N s
  rw [leftRepairMinor, LocalRepairClosure.boundaryMinor,
    Matroid.isBase_restrict_iff (hX := Set.union_subset hiGround hjGround)]
  exact hcontract.isBasis_of_subset
    (hX := Set.union_subset hiGround hjGround) Set.subset_union_left

/-- The right modified block is a base of the right repair minor. -/
theorem right_block_isBase_rightRepairMinor
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    (rightRepairMinor A s).IsBase
      (A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s)) := by
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  have hdis : Disjoint (A.block j) (A.core j) :=
    A.block_disjoint_core (by omega) h2N j
  have hbase : M.IsBase (A.block j ∪ A.core j) :=
    A.endpoint_basis_left (by omega) j
  have hcontract : (M.contract (A.core j)).IsBase (A.block j) :=
    (A.core_indep (by omega) j).contract_isBase_iff.2 ⟨hbase, hdis⟩
  have hjGround : A.block j ⊆ (M.contract (A.core j)).E := hcontract.subset_ground
  have hiGround :
      A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) ⊆
        (M.contract (A.core j)).E := by
    simpa [j] using left_block_subset_right_contract_ground A h2N s
  rw [rightRepairMinor, LocalRepairClosure.boundaryMinor,
    Matroid.isBase_restrict_iff (hX := Set.union_subset hiGround hjGround)]
  exact hcontract.isBasis_of_subset
    (hX := Set.union_subset hiGround hjGround) Set.subset_union_right

/-- In the right boundary minor, the complement of the left modified block is
exactly the right modified block. -/
theorem repairGround_sdiff_left_block
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    repairGround A s \ A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) =
      A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s) := by
  ext x
  constructor
  · rintro ⟨hx, hxnot⟩
    rcases hx with hxleft | hxright
    · exact (hxnot hxleft).elim
    · exact hxright
  · intro hxright
    refine ⟨Or.inr hxright, ?_⟩
    intro hxleft
    exact Set.disjoint_left.1 (modified_blocks_disjoint A h2N s) hxleft hxright

/-- The current left pair is a base of the dual right repair minor. -/
theorem left_block_isBase_dual_rightRepairMinor
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    (rightRepairMinor A s)✶.IsBase
      (A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s)) := by
  have hsub : A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) ⊆ repairGround A s :=
    Set.subset_union_left
  apply (AdjacentRepair.complement_isBase_iff_dual_isBase
    (rightRepairMinor A s) (by simp [rightRepairMinor, LocalRepairClosure.boundaryMinor]) hsub).1
  rw [repairGround_sdiff_left_block A h2N s]
  exact right_block_isBase_rightRepairMinor A h2N s

/-- Rank-four cycle-specific closure obstruction. If the current adjacent
2+2 repartition is the unique common base of the two rank-two boundary
matroids, then some moved element is spanned by the unchanged neighboring
core on the left or right. -/
theorem unique_adjacent_repartition_forces_neighbor_closure
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (hunique : ∀ Q : Set α,
      (leftRepairMinor A s).IsBase Q →
      (rightRepairMinor A s)✶.IsBase Q →
      Q = A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s)) :
    A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false ∈ M.closure (A.core s) ∨
    A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true ∈ M.closure (A.core s) ∨
    A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false ∈
      M.closure (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s)) ∨
    A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true ∈
      M.closure (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s)) := by
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  have hdis : Disjoint
      ({A.element i false, A.element i true} : Set α)
      ({A.element j false, A.element j true} : Set α) := by
    simpa [i, j, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      modified_blocks_disjoint A h2N s
  have hc₀L : A.element j false ∈ (M.contract (A.core s)).E :=
    right_block_subset_left_contract_ground A h2N s (by simp [j, AdmissiblePairCycle.Data.block,
      AdmissiblePairCycle.pairSet])
  have hc₁L : A.element j true ∈ (M.contract (A.core s)).E :=
    right_block_subset_left_contract_ground A h2N s (by simp [j, AdmissiblePairCycle.Data.block,
      AdmissiblePairCycle.pairSet])
  have hb₀R : A.element i false ∈ (M.contract (A.core j)).E := by
    exact left_block_subset_right_contract_ground A h2N s
      (by simp [i, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet])
  have hb₁R : A.element i true ∈ (M.contract (A.core j)).E := by
    exact left_block_subset_right_contract_ground A h2N s
      (by simp [i, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet])
  have hclosure := LocalRepairClosure.unique_local_repair_forces_ambient_closure
    M (CL := A.core s) (CR := A.core j)
    (b₀ := A.element i false) (b₁ := A.element i true)
    (c₀ := A.element j false) (c₁ := A.element j true)
    (A.element_ne i) (A.element_ne j) hdis
    hc₀L hc₁L hb₀R hb₁R
    (by simpa [leftRepairMinor, repairGround, i, j,
      AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      left_block_isBase_leftRepairMinor A h2N s)
    (by simpa [rightRepairMinor, repairGround, i, j,
      AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      left_block_isBase_dual_rightRepairMinor A h2N s)
    (by
      intro Q hLQ hRQ
      have hEq := hunique Q (by simpa [leftRepairMinor, repairGround, i, j,
        AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using hLQ)
        (by simpa [rightRepairMinor, repairGround, i, j,
          AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using hRQ)
      simpa [i, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using hEq)
  simpa [i, j] using hclosure

end Rank4GcdTwoRepair
end HigherRankKUM
