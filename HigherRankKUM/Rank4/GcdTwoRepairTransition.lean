import HigherRankKUM.PairBlockPartitionReplace
import HigherRankKUM.Rank4.GcdTwoRepairState

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open PairCycleIndexing

variable {α : Type*}

/-- The two adjacent pair indices modified by a rank-four local repair are
distinct whenever the pair cycle has more than two blocks. -/
theorem modified_indices_ne
    {N : ℕ} {hN : 0 < N} (h2N : 2 < N) (s : Fin N) :
    AdjacentRepair.leftBoundaryIndex N 2 hN s ≠
      AdjacentRepair.rightBoundaryIndex N 2 hN s := by
  rw [rightBoundaryIndex_eq_next_leftBoundaryIndex (N := N) (hN := hN) s]
  exact (cyclicIndex_ne_self_of_pos_of_lt N hN
    (AdjacentRepair.leftBoundaryIndex N 2 hN s) (by omega) (by omega)).symm

/-- Forget the old Boolean labels, replace the two repaired blocks by the
`LocalRepartition`, and retain all untouched blocks.  The result is again a
partition of the same matroid ground set into labelled pairs. -/
noncomputable def repairedPairPartition
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (R : LocalRepartition A s) : PairBlockPartition.Data M N := by
  let P := PairBlockPartition.ofAdmissiblePairCycle A
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  apply P.replaceTwo i j (modified_indices_ne h2N s)
    R.leftBlock R.rightBlock R.leftCard R.rightCard R.disjoint
  simpa [P, i, j, repairGround, PairBlockPartition.ofAdmissiblePairCycle] using R.union_eq

@[simp] theorem repairedPairPartition_left_block
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (R : LocalRepartition A s) :
    (repairedPairPartition A h2N s R).block
      (AdjacentRepair.leftBoundaryIndex N 2 hN s) = R.leftBlock := by
  simp [repairedPairPartition, PairBlockPartition.Data.replaceTwo]

@[simp] theorem repairedPairPartition_right_block
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (R : LocalRepartition A s) :
    (repairedPairPartition A h2N s R).block
      (AdjacentRepair.rightBoundaryIndex N 2 hN s) = R.rightBlock := by
  simp [repairedPairPartition, PairBlockPartition.Data.replaceTwo,
    modified_indices_ne h2N s]

@[simp] theorem repairedPairPartition_other_block
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (R : LocalRepartition A s) (k : Fin N)
    (hki : k ≠ AdjacentRepair.leftBoundaryIndex N 2 hN s)
    (hkj : k ≠ AdjacentRepair.rightBoundaryIndex N 2 hN s) :
    (repairedPairPartition A h2N s R).block k = A.block k := by
  simp [repairedPairPartition, PairBlockPartition.Data.replaceTwo, hki, hkj]

/-- Global Boolean labelling of the repaired pair partition.  The labels inside
each two-element block are deliberately noncomputable and irrelevant; the
important invariant is the recovered pair set at every block index. -/
noncomputable def repairedPairEquiv
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (R : LocalRepartition A s) : Fin N × Bool ≃ M.E :=
  (repairedPairPartition A h2N s R).pairEquiv

/-- The new equivalence recovers the repaired left block exactly. -/
theorem repairedPairEquiv_left_pairSet
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (R : LocalRepartition A s) :
    AdmissiblePairCycle.pairSet (repairedPairEquiv A h2N s R)
      (AdjacentRepair.leftBoundaryIndex N 2 hN s) = R.leftBlock := by
  rw [repairedPairEquiv]
  rw [PairBlockPartition.Data.pairSet_pairEquiv_eq_block]
  exact repairedPairPartition_left_block A h2N s R

/-- The new equivalence recovers the repaired right block exactly. -/
theorem repairedPairEquiv_right_pairSet
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (R : LocalRepartition A s) :
    AdmissiblePairCycle.pairSet (repairedPairEquiv A h2N s R)
      (AdjacentRepair.rightBoundaryIndex N 2 hN s) = R.rightBlock := by
  rw [repairedPairEquiv]
  rw [PairBlockPartition.Data.pairSet_pairEquiv_eq_block]
  exact repairedPairPartition_right_block A h2N s R

/-- Every untouched pair set is unchanged by the new global equivalence. -/
theorem repairedPairEquiv_other_pairSet
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (R : LocalRepartition A s) (k : Fin N)
    (hki : k ≠ AdjacentRepair.leftBoundaryIndex N 2 hN s)
    (hkj : k ≠ AdjacentRepair.rightBoundaryIndex N 2 hN s) :
    AdmissiblePairCycle.pairSet (repairedPairEquiv A h2N s R) k = A.block k := by
  rw [repairedPairEquiv]
  rw [PairBlockPartition.Data.pairSet_pairEquiv_eq_block]
  exact repairedPairPartition_other_block A h2N s R k hki hkj

end Rank4GcdTwoRepair
end HigherRankKUM
