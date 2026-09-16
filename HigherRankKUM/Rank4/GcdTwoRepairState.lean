import HigherRankKUM.Rank4.GcdTwoRepairGeometry

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

variable {α : Type*}

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

end Rank4GcdTwoRepair
end HigherRankKUM
