import HigherRankKUM.Rank4.ThreePairDual
import HigherRankKUM.BinaryRelationGauge

namespace HigherRankKUM
namespace Rank4ThreePairDual

open Set
open BinaryRelationCycle
open PairCycle

variable {α : Type*}

/-- Two nondegenerate Boolean labellings of the same two-element set differ
by exactly one Boolean swap.  This is the choice-independence bridge used for
noncomputably relabelled repaired pair blocks. -/
theorem pair_labels_eq_bitPick_of_pair_eq
    {a₀ a₁ b₀ b₁ : α}
    (_ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    (hpair : ({b₀, b₁} : Set α) = {a₀, a₁}) :
    ∃ p : Bool,
      b₀ = bitPick a₀ a₁ p ∧
      b₁ = bitPick a₀ a₁ (Bool.not p) := by
  have hb₀mem : b₀ ∈ ({a₀, a₁} : Set α) := by
    rw [← hpair]
    simp
  have hb₁mem : b₁ ∈ ({a₀, a₁} : Set α) := by
    rw [← hpair]
    simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb₀mem hb₁mem
  rcases hb₀mem with h₀ | h₀
  · have h₁ : b₁ = a₁ := by
      rcases hb₁mem with h | h
      · exact (hb (h₀.trans h.symm)).elim
      · exact h
    subst b₀
    subst b₁
    exact ⟨false, by simp [bitPick]⟩
  · have h₁ : b₁ = a₀ := by
      rcases hb₁mem with h | h
      · exact h
      · exact (hb (h₀.trans h.symm)).elim
    subst b₀
    subst b₁
    exact ⟨true, by simp [bitPick]⟩

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
    change M.IsBase
        ({bitPick x₀ x₁ x, y₁, y₀, bitPick z₀ z₁ z} : Set α) ↔
      M.IsBase
        ({bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z} : Set α)
    rw [hset]

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

/-- Relabelling all three pair blocks acts only through the endpoint gauges.
The middle pair is consumed as a whole, so its internal Boolean order drops
out completely. -/
theorem middlePairRelation_relabel_all
    (M : Matroid α) (x₀ x₁ y₀ y₁ z₀ z₁ : α) (p q r : Bool) :
    middlePairRelation M
        (bitPick x₀ x₁ p) (bitPick x₀ x₁ (Bool.not p))
        (bitPick y₀ y₁ q) (bitPick y₀ y₁ (Bool.not q))
        (bitPick z₀ z₁ r) (bitPick z₀ z₁ (Bool.not r)) =
      gaugeRelation p r (middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁) := by
  rw [middlePairRelation_relabel_middle]
  rw [middlePairRelation_relabel_endpoints]
  rfl

end Rank4ThreePairDual
end HigherRankKUM
