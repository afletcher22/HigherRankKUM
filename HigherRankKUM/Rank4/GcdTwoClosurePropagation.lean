import HigherRankKUM.Rank4.GcdTwoRepairGeometry

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open PairCycleIndexing

variable {α : Type*}

/-- Some element of the block two cyclic positions ahead lies in the rank-two
flat spanned by the current block. This is the natural directed closure edge
on the `+2` block orbit in the rank-four gcd-two model. -/
def ForwardDistanceTwoClosure
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (i : Fin N) : Prop :=
  ∃ b : Bool,
    A.element (cyclicIndex N hN i 2) b ∈ M.closure (A.block i)

/-- The reverse directed closure edge between the same two distance-two
blocks. -/
def BackwardDistanceTwoClosure
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (i : Fin N) : Prop :=
  ∃ b : Bool,
    A.element i b ∈ M.closure (A.block (cyclicIndex N hN i 2))

/-- Orbit-level form of the Sprint 3 rigidity theorem.

If the current `2+2` repartition is the unique common base at boundary `s`,
then one of the two neighboring edges of the `+2` block orbit carries a
directed ambient-closure incidence: either forward from block `s+1` to
`s+3`, or backward from block `s+4` to `s+2`. -/
theorem unique_boundary_forces_distanceTwoClosure
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (hunique : ∀ Q : Set α,
      (leftRepairMinor A s).IsBase Q →
      (rightRepairMinor A s)✶.IsBase Q →
      Q = A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s)) :
    ForwardDistanceTwoClosure A (cyclicIndex N hN s 1) ∨
      BackwardDistanceTwoClosure A (cyclicIndex N hN s 2) := by
  rcases unique_adjacent_repartition_forces_neighbor_closure A h2N s hunique with
    h | h | h | h
  · left
    refine ⟨false, ?_⟩
    rw [core_eq_next_block A s] at h
    simpa [ForwardDistanceTwoClosure, AdjacentRepair.rightBoundaryIndex,
      cyclicIndex_add] using h
  · left
    refine ⟨true, ?_⟩
    rw [core_eq_next_block A s] at h
    simpa [ForwardDistanceTwoClosure, AdjacentRepair.rightBoundaryIndex,
      cyclicIndex_add] using h
  · right
    refine ⟨false, ?_⟩
    rw [core_eq_next_block A
      (AdjacentRepair.rightBoundaryIndex N 2 hN s)] at h
    simpa [BackwardDistanceTwoClosure, AdjacentRepair.leftBoundaryIndex,
      AdjacentRepair.rightBoundaryIndex, cyclicIndex_add] using h
  · right
    refine ⟨true, ?_⟩
    rw [core_eq_next_block A
      (AdjacentRepair.rightBoundaryIndex N 2 hN s)] at h
    simpa [BackwardDistanceTwoClosure, AdjacentRepair.leftBoundaryIndex,
      AdjacentRepair.rightBoundaryIndex, cyclicIndex_add] using h

/-- Local contrapositive of rigidity. If neither of the two closure incidences
that could certify rigidity is present, then the boundary admits a genuinely
alternative common-base repartition.

This is a first productive-boundary criterion stated directly on the `+2`
block orbit; it avoids the global closure-potential averaging argument. -/
theorem exists_alternative_repartition_of_no_distanceTwoClosure
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (hforward : ¬ ForwardDistanceTwoClosure A (cyclicIndex N hN s 1))
    (hbackward : ¬ BackwardDistanceTwoClosure A (cyclicIndex N hN s 2)) :
    ∃ Q : Set α,
      (leftRepairMinor A s).IsBase Q ∧
      (rightRepairMinor A s)✶.IsBase Q ∧
      Q ≠ A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) := by
  by_contra hno
  have hunique : ∀ Q : Set α,
      (leftRepairMinor A s).IsBase Q →
      (rightRepairMinor A s)✶.IsBase Q →
      Q = A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) := by
    intro Q hL hR
    by_contra hne
    exact hno ⟨Q, hL, hR, hne⟩
  rcases unique_boundary_forces_distanceTwoClosure A h2N s hunique with
    hf | hb
  · exact hforward hf
  · exact hbackward hb

end Rank4GcdTwoRepair
end HigherRankKUM