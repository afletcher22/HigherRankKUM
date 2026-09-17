import HigherRankKUM.Rank4.ThreePairDual

namespace HigherRankKUM
namespace Rank4ThreePairDual

open BinaryRelationCycle
open PairCycle

variable {α : Type*}

/-- Swapping the labels of the left endpoint pair is exactly an input
relabelling of the middle-pair relation. -/
theorem middlePairRelation_relabel_left
    (M : Matroid α) (x₀ x₁ y₀ y₁ z₀ z₁ : α) (b : Bool) :
    middlePairRelation M
        (bitPick x₀ x₁ b) (bitPick x₀ x₁ (Bool.not b))
        y₀ y₁ z₀ z₁ =
      relabelInput b (middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁) := by
  funext x z
  apply propext
  cases b <;> cases x <;>
    simp [middlePairRelation, relabelInput, bitPick]

/-- Swapping the labels of the right endpoint pair is exactly an output
relabelling of the middle-pair relation. -/
theorem middlePairRelation_relabel_right
    (M : Matroid α) (x₀ x₁ y₀ y₁ z₀ z₁ : α) (b : Bool) :
    middlePairRelation M x₀ x₁ y₀ y₁
        (bitPick z₀ z₁ b) (bitPick z₀ z₁ (Bool.not b)) =
      relabelOutput b (middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁) := by
  funext x z
  apply propext
  cases b <;> cases z <;>
    simp [middlePairRelation, relabelOutput, bitPick]

/-- The order of the two labels on the whole middle pair is irrelevant. -/
theorem middlePairRelation_relabel_middle
    (M : Matroid α) (x₀ x₁ y₀ y₁ z₀ z₁ : α) (b : Bool) :
    middlePairRelation M x₀ x₁
        (bitPick y₀ y₁ b) (bitPick y₀ y₁ (Bool.not b)) z₀ z₁ =
      middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁ := by
  cases b
  · simp [middlePairRelation, bitPick]
  · funext x z
    apply propext
    have hset :
        ({bitPick x₀ x₁ x, y₁, y₀, bitPick z₀ z₁ z} : Set α) =
          {bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z} := by
      ext t
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    simpa [middlePairRelation, bitPick, hset]

/-- Simultaneous arbitrary relabelling of the endpoint pairs.  The middle
pair may be relabelled independently without changing the relation. -/
theorem middlePairRelation_relabel_endpoints
    (M : Matroid α) (x₀ x₁ y₀ y₁ z₀ z₁ : α) (p q : Bool) :
    middlePairRelation M
        (bitPick x₀ x₁ p) (bitPick x₀ x₁ (Bool.not p))
        y₀ y₁
        (bitPick z₀ z₁ q) (bitPick z₀ z₁ (Bool.not q)) =
      relabelInput p
        (relabelOutput q (middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁)) := by
  funext x z
  apply propext
  cases p <;> cases q <;> cases x <;> cases z <;>
    simp [middlePairRelation, relabelInput, relabelOutput, bitPick]

end Rank4ThreePairDual
end HigherRankKUM
