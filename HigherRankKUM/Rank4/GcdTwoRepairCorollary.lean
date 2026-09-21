import HigherRankKUM.Rank4.GcdTwoRepairGeometry

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

variable {α : Type*}

/-- Operational contrapositive of the rank-four local rigidity theorem.
If none of the four possible neighbor-closure obstructions occurs, then the
current left pair cannot be the unique common base of the two boundary
matroids: there is another admissible local `2+2` repartition.

The conclusion deliberately allows the opposite whole-block swap.  A
closure-free boundary does not, by itself, force a single-element cross
exchange. -/
theorem exists_alternative_repartition_of_neighbor_closure_free
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (hj₀ : A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false ∉
      M.closure (A.core s))
    (hj₁ : A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true ∉
      M.closure (A.core s))
    (hi₀ : A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false ∉
      M.closure (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s)))
    (hi₁ : A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true ∉
      M.closure (A.core (AdjacentRepair.rightBoundaryIndex N 2 hN s))) :
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
  rcases unique_adjacent_repartition_forces_neighbor_closure A h2N s hunique with
    h | h | h | h
  · exact hj₀ h
  · exact hj₁ h
  · exact hi₀ h
  · exact hi₁ h

end Rank4GcdTwoRepair
end HigherRankKUM
