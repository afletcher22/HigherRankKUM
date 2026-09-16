import HigherRankKUM.Rank4.GcdTwoRepairGeometry

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

variable {α : Type*}

/-- The current left repair block is already a base of the full left boundary
contraction, before restricting to the four moved elements. -/
theorem left_block_isBase_left_contract
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    (M.contract (A.core s)).IsBase
      (A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s)) := by
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  have hdis : Disjoint (A.block i) (A.core s) := by
    simpa [i, AdjacentRepair.leftBoundaryIndex,
      AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      A.endpoint_block_disjoint_core (by omega) h2N s
  have hbase : M.IsBase (A.block i ∪ A.core s) := by
    simpa [i, AdjacentRepair.leftBoundaryIndex] using
      A.endpoint_basis_right (by omega) s
  exact (A.core_indep (by omega) s).contract_isBase_iff.2 ⟨hbase, hdis⟩

/-- The current right repair block is already a base of the full right boundary
contraction. -/
theorem right_block_isBase_right_contract
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N) :
    (M.contract (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s))).IsBase
      (A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s)) := by
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  have hdis : Disjoint (A.block j) (A.core j) :=
    A.block_disjoint_core (by omega) h2N j
  have hbase : M.IsBase (A.block j ∪ A.core j) :=
    A.endpoint_basis_left (by omega) j
  simpa [j] using
    (A.core_indep (by omega) j).contract_isBase_iff.2 ⟨hbase, hdis⟩

/-- A common base `Q` of the two rank-two repair boundary matroids is exactly a
new two-element left block, while its complement in the four-element repair
ground is exactly a new two-element right block.

This is the finite set-theoretic bridge needed before constructing a repaired
`AdmissiblePairCycle.Data`: the abstract common-base witness really is a
replacement `2+2` partition of the same four moved ground elements. -/
theorem common_base_repartition_pair_decomposition
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    {Q : Set α}
    (hL : (leftRepairMinor A s).IsBase Q)
    (hR : (rightRepairMinor A s)✶.IsBase Q) :
    ∃ q₀ q₁ r₀ r₁ : α,
      q₀ ≠ q₁ ∧ r₀ ≠ r₁ ∧
      Q = {q₀, q₁} ∧
      repairGround A s \ Q = {r₀, r₁} ∧
      repairGround A s = ({q₀, q₁} : Set α) ∪ {r₀, r₁} := by
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  have hQsub : Q ⊆ repairGround A s := by
    have hsub := hL.subset_ground
    simpa [leftRepairMinor, LocalRepairClosure.boundaryMinor] using hsub
  have hleftCurrent :
      (leftRepairMinor A s).IsBase (A.block i) := by
    simpa [i] using left_block_isBase_leftRepairMinor A h2N s
  have hQcard : Q.encard = 2 := by
    calc
      Q.encard = (A.block i).encard := hL.encard_eq_encard_of_isBase hleftCurrent
      _ = 2 := by
        simp [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet,
          A.element_ne i]
  have hcompBase :
      (rightRepairMinor A s).IsBase (repairGround A s \ Q) := by
    exact (AdjacentRepair.complement_isBase_iff_dual_isBase
      (rightRepairMinor A s)
      (by simp [rightRepairMinor, LocalRepairClosure.boundaryMinor])
      hQsub).2 hR
  have hrightCurrent :
      (rightRepairMinor A s).IsBase (A.block j) := by
    simpa [j] using right_block_isBase_rightRepairMinor A h2N s
  have hcompCard : (repairGround A s \ Q).encard = 2 := by
    calc
      (repairGround A s \ Q).encard = (A.block j).encard :=
        hcompBase.encard_eq_encard_of_isBase hrightCurrent
      _ = 2 := by
        simp [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet,
          A.element_ne j]
  obtain ⟨q₀, q₁, hqne, hQ⟩ := Set.encard_eq_two.mp hQcard
  obtain ⟨r₀, r₁, hrne, hRcomp⟩ := Set.encard_eq_two.mp hcompCard
  refine ⟨q₀, q₁, r₀, r₁, hqne, hrne, hQ, hRcomp, ?_⟩
  have hpartition : Q ∪ (repairGround A s \ Q) = repairGround A s := by
    apply Set.Subset.antisymm
    · exact Set.union_subset hQsub Set.sdiff_subset
    · intro x hx
      by_cases hxQ : x ∈ Q
      · exact Or.inl hxQ
      · exact Or.inr ⟨hx, hxQ⟩
  simpa [hQ, hRcomp] using hpartition.symm

/-- The two common-base conditions on the restricted repair minors promote to
the two ambient rank-four basis conditions that can actually replace the
corresponding pair blocks in the admissible pair cycle. -/
theorem common_base_repartition_ambient_boundary_bases
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    {Q : Set α}
    (hL : (leftRepairMinor A s).IsBase Q)
    (hR : (rightRepairMinor A s)✶.IsBase Q) :
    M.IsBase (Q ∪ A.core s) ∧
    M.IsBase ((repairGround A s \ Q) ∪
      A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s)) := by
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  obtain ⟨q₀, q₁, r₀, r₁, hqne, hrne, hQ, hRcomp, _hpartition⟩ :=
    common_base_repartition_pair_decomposition A h2N s hL hR
  have hQind : (M.contract (A.core s)).Indep Q := by
    have hI := hL.indep
    rw [leftRepairMinor, LocalRepairClosure.boundaryMinor,
      Matroid.restrict_indep_iff] at hI
    exact hI.1
  have hleftPairBase :
      (M.contract (A.core s)).IsBase
        {A.element i false, A.element i true} := by
    simpa [i, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      left_block_isBase_left_contract A h2N s
  have hQcontract : (M.contract (A.core s)).IsBase Q := by
    rw [hQ]
    apply AdjacentRepair.pair_indep_isBase_of_pair_isBase
      (M.contract (A.core s)) (A.element_ne i) hqne hleftPairBase
    simpa [hQ] using hQind
  have hQsub : Q ⊆ repairGround A s := by
    have hsub := hL.subset_ground
    simpa [leftRepairMinor, LocalRepairClosure.boundaryMinor] using hsub
  have hcompRestrict :
      (rightRepairMinor A s).IsBase (repairGround A s \ Q) := by
    exact (AdjacentRepair.complement_isBase_iff_dual_isBase
      (rightRepairMinor A s)
      (by simp [rightRepairMinor, LocalRepairClosure.boundaryMinor])
      hQsub).2 hR
  have hcompInd :
      (M.contract (A.core j)).Indep (repairGround A s \ Q) := by
    have hI := hcompRestrict.indep
    rw [rightRepairMinor, LocalRepairClosure.boundaryMinor,
      Matroid.restrict_indep_iff] at hI
    simpa [j] using hI.1
  have hrightPairBase :
      (M.contract (A.core j)).IsBase
        {A.element j false, A.element j true} := by
    simpa [j, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      right_block_isBase_right_contract A h2N s
  have hcompContract :
      (M.contract (A.core j)).IsBase (repairGround A s \ Q) := by
    rw [hRcomp]
    apply AdjacentRepair.pair_indep_isBase_of_pair_isBase
      (M.contract (A.core j)) (A.element_ne j) hrne hrightPairBase
    simpa [hRcomp] using hcompInd
  refine ⟨?_, ?_⟩
  · exact ((A.core_indep (by omega) s).contract_isBase_iff.1 hQcontract).1
  · simpa [j] using
      ((A.core_indep (by omega) j).contract_isBase_iff.1 hcompContract).1

end Rank4GcdTwoRepair
end HigherRankKUM
