import HigherRankKUM.Rank4.GcdTwoRepairDichotomy
import HigherRankKUM.BinaryRelationParity

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

variable {α : Type*}

/-- The exceptional swap-only boundary geometry is not merely a pair of
bijection relations: the two boundary relations are exactly the two
complementary perfect matchings of the Boolean square.

This strengthening is representation-free.  It combines the local matroid
rigidity theorem with the complete two-state classification of disjoint
bijections; no binary or linear representation is assumed. -/
theorem swap_only_crossRelations_are_complementary
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (s : Fin N) {Q : Set α} (hswap : IsSwapCommonBase A s Q)
    (hnoCrossCell : ∀ x y,
      ¬ (leftBoundaryCrossRelation A s x y ∧
        dualRightBoundaryCrossRelation A s x y)) :
    ((leftBoundaryCrossRelation A s = BinaryRelationCycle.idRel ∧
        dualRightBoundaryCrossRelation A s = BinaryRelationCycle.flipRel) ∨
      (leftBoundaryCrossRelation A s = BinaryRelationCycle.flipRel ∧
        dualRightBoundaryCrossRelation A s = BinaryRelationCycle.idRel)) := by
  obtain ⟨hL, hR⟩ :=
    swap_only_crossRelations_are_bijections A h2N s hswap hnoCrossCell
  exact BinaryRelationCycle.complementary_of_disjoint_bijections hL hR hnoCrossCell

end Rank4GcdTwoRepair
end HigherRankKUM
