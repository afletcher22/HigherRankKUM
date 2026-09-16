import HigherRankKUM.Rank4.GcdTwoRepairCorollary
import HigherRankKUM.PotentialAscent

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open scoped BigOperators

variable {α : Type*}

/-- Natural-valued indicator of a proposition.  It is kept as a separate
notion so the closure potential below is visibly a sum of the exact four
ambient-closure incidences occurring in the Sprint 3 rigidity theorem. -/
noncomputable def closureIndicator (p : Prop) : ℕ := by
  classical
  exact if p then 1 else 0

@[simp] theorem closureIndicator_eq_one_iff (p : Prop) :
    closureIndicator p = 1 ↔ p := by
  classical
  simp [closureIndicator]

@[simp] theorem closureIndicator_eq_zero_iff (p : Prop) :
    closureIndicator p = 0 ↔ ¬ p := by
  classical
  simp [closureIndicator]

theorem closureIndicator_le_one (p : Prop) : closureIndicator p ≤ 1 := by
  classical
  simp [closureIndicator]

/-- The four local neighbor-closure incidences attached to the repair boundary
indexed by `s`.  In rank four the two unchanged cores are pair blocks, so this
is the local contribution to the closure score suggested by the Sprint 4
finite experiments. -/
noncomputable def boundaryClosureScore
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) : ℕ :=
  closureIndicator
      (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false ∈
        M.closure (A.core s)) +
  closureIndicator
      (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true ∈
        M.closure (A.core s)) +
  closureIndicator
      (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false ∈
        M.closure (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s))) +
  closureIndicator
      (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true ∈
        M.closure (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s)))

/-- Global closure potential: sum the four Sprint 3 obstruction incidences over
all cyclic repair boundaries. -/
noncomputable def closurePotential
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) : ℕ :=
  ∑ s : Fin N, boundaryClosureScore A s

/-- One boundary contributes at most four to the global closure potential. -/
theorem boundaryClosureScore_le_four
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) :
    boundaryClosureScore A s ≤ 4 := by
  have h₁ := closureIndicator_le_one
    (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false ∈
      M.closure (A.core s))
  have h₂ := closureIndicator_le_one
    (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true ∈
      M.closure (A.core s))
  have h₃ := closureIndicator_le_one
    (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false ∈
      M.closure (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s)))
  have h₄ := closureIndicator_le_one
    (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true ∈
      M.closure (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s)))
  simp only [boundaryClosureScore]
  omega

/-- Hence the global potential is bounded by `4N`.  This is the boundedness
input needed by the generic `PotentialAscent` termination theorem. -/
theorem closurePotential_le_four_mul
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) :
    closurePotential A ≤ 4 * N := by
  classical
  rw [closurePotential]
  calc
    (∑ s : Fin N, boundaryClosureScore A s) ≤ ∑ _s : Fin N, 4 := by
      apply Finset.sum_le_sum
      intro s hs
      exact boundaryClosureScore_le_four A s
    _ = 4 * N := by simp [Nat.mul_comm]

/-- A unique local repartition has positive closure score, directly by the
Sprint 3 rank-four rigidity theorem. -/
theorem boundaryClosureScore_pos_of_unique
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (hunique : ∀ Q : Set α,
      (leftRepairMinor A s).IsBase Q →
      (rightRepairMinor A s)✶.IsBase Q →
      Q = A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s)) :
    0 < boundaryClosureScore A s := by
  classical
  rcases unique_adjacent_repartition_forces_neighbor_closure A h2N s hunique with
    h | h | h | h
  · simp [boundaryClosureScore, closureIndicator, h]
  · simp [boundaryClosureScore, closureIndicator, h]
  · simp [boundaryClosureScore, closureIndicator, h]
  · simp [boundaryClosureScore, closureIndicator, h]

/-- If every repair boundary is rigid (the current pair is its unique common
base), then the global closure potential is at least the number of pair
blocks. -/
theorem card_le_closurePotential_of_all_unique
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (hunique : ∀ s : Fin N, ∀ Q : Set α,
      (leftRepairMinor A s).IsBase Q →
      (rightRepairMinor A s)✶.IsBase Q →
      Q = A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s)) :
    N ≤ closurePotential A := by
  classical
  rw [closurePotential]
  calc
    N = ∑ _s : Fin N, 1 := by simp
    _ ≤ ∑ s : Fin N, boundaryClosureScore A s := by
      apply Finset.sum_le_sum
      intro s hs
      have hpos := boundaryClosureScore_pos_of_unique A h2N s (hunique s)
      omega

/-- First global consequence of the closure potential.  If the total number of
neighbor-closure incidences is below `N`, not every boundary can be rigid:
some boundary admits an alternative common-base `2+2` repartition.

This is deliberately weaker than the experimental strict-ascent statement.  It
is a theorem for arbitrary matroids carrying the admissible pair-cycle data,
with no representability assumption. -/
theorem exists_alternative_repartition_of_closurePotential_lt_card
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (hlt : closurePotential A < N) :
    ∃ s : Fin N, ∃ Q : Set α,
      (leftRepairMinor A s).IsBase Q ∧
      (rightRepairMinor A s)✶.IsBase Q ∧
      Q ≠ A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) := by
  classical
  by_contra hno
  have hunique : ∀ s : Fin N, ∀ Q : Set α,
      (leftRepairMinor A s).IsBase Q →
      (rightRepairMinor A s)✶.IsBase Q →
      Q = A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) := by
    intro s Q hL hR
    by_contra hne
    exact hno ⟨s, Q, hL, hR, hne⟩
  have hge := card_le_closurePotential_of_all_unique A h2N hunique
  omega

end Rank4GcdTwoRepair
end HigherRankKUM
