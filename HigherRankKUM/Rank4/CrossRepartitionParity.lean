import HigherRankKUM.Rank4.ThreePairDual

namespace HigherRankKUM
namespace Rank4ThreePairDual

open Set
open BinaryRelationCycle
open PairCycle

variable {α : Type*}

/-- Representation-free parity conservation for all four cross repartitions
of two adjacent pair blocks.

Let the old consecutive blocks be `A,B,C,D,E,F`.  For Boolean parameters
`u,v`, repartition `C ∪ D` into

`Q = (c_u,d_v)` and `R = (c_{¬u},d_{¬v})`.

If the four old and four new affected middle-pair relations are forced
Boolean bijections, then cyclic satisfiability of the affected four-cycle is
preserved.  The four new relations are respectively an output relabelling by
`u`, an output relabelling by `v`, an input relabelling by `u`, and an input
relabelling by `v` of the old relations.

The proof uses only shared basis cells plus forcedness; no field,
representability, disjointness, or ambient-rank hypothesis is required. -/
theorem crossRepartition_middlePairRelations_preserve_cyclicSatisfiable
    (M : Matroid α)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ e₀ e₁ f₀ f₁ : α}
    (u v : Bool)
    (hR₁ : BijectionRelation (middlePairRelation M a₀ a₁ b₀ b₁ c₀ c₁))
    (hR₂ : BijectionRelation (middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁))
    (hR₃ : BijectionRelation (middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁))
    (hR₄ : BijectionRelation (middlePairRelation M d₀ d₁ e₀ e₁ f₀ f₁))
    (hS₁ : BijectionRelation
      (middlePairRelation M a₀ a₁ b₀ b₁
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)))
    (hS₂ : BijectionRelation
      (middlePairRelation M b₀ b₁
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))))
    (hS₃ : BijectionRelation
      (middlePairRelation M
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
        e₀ e₁))
    (hS₄ : BijectionRelation
      (middlePairRelation M
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
        e₀ e₁ f₀ f₁)) :
    CyclicSatisfiable
      [middlePairRelation M a₀ a₁ b₀ b₁ c₀ c₁,
       middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁,
       middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁,
       middlePairRelation M d₀ d₁ e₀ e₁ f₀ f₁] ↔
    CyclicSatisfiable
      [middlePairRelation M a₀ a₁ b₀ b₁
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v),
       middlePairRelation M b₀ b₁
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v)),
       middlePairRelation M
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
        e₀ e₁,
       middlePairRelation M
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
        e₀ e₁ f₀ f₁] := by
  have hS₁eq :
      middlePairRelation M a₀ a₁ b₀ b₁
          (bitPick c₀ c₁ u) (bitPick d₀ d₁ v) =
        relabelOutput u (middlePairRelation M a₀ a₁ b₀ b₁ c₀ c₁) := by
    apply eq_of_bijections_of_agree_output_false hS₁
      (relabelOutput_bijection u hR₁)
    intro x
    cases u <;> simp [middlePairRelation, relabelOutput, bitPick]

  have hset₂ (x : Bool) :
      ({bitPick b₀ b₁ x,
        bitPick c₀ c₁ u,
        bitPick d₀ d₁ v,
        bitPick c₀ c₁ (Bool.not u)} : Set α) =
      ({bitPick b₀ b₁ x, c₀, c₁, bitPick d₀ d₁ v} : Set α) := by
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    cases u <;> simp [bitPick] <;> tauto

  have hS₂eq :
      middlePairRelation M b₀ b₁
          (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
          (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v)) =
        relabelOutput v (middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁) := by
    apply eq_of_bijections_of_agree_output_false hS₂
      (relabelOutput_bijection v hR₂)
    intro x
    change
      M.IsBase
          ({bitPick b₀ b₁ x,
            bitPick c₀ c₁ u,
            bitPick d₀ d₁ v,
            bitPick c₀ c₁ (Bool.not u)} : Set α) ↔
        relabelOutput v (middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁) x false
    rw [hset₂ x]
    cases v <;> simp [middlePairRelation, relabelOutput, bitPick]

  have hset₃ (y : Bool) :
      ({bitPick d₀ d₁ v,
        bitPick c₀ c₁ (Bool.not u),
        bitPick d₀ d₁ (Bool.not v),
        bitPick e₀ e₁ y} : Set α) =
      ({bitPick c₀ c₁ (Bool.not u), d₀, d₁, bitPick e₀ e₁ y} : Set α) := by
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    cases v <;> simp [bitPick] <;> tauto

  have hS₃eq :
      middlePairRelation M
          (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
          (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
          e₀ e₁ =
        relabelInput u (middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁) := by
    apply eq_of_bijections_of_agree_input_true hS₃
      (relabelInput_bijection u hR₃)
    intro y
    change
      M.IsBase
          ({bitPick d₀ d₁ v,
            bitPick c₀ c₁ (Bool.not u),
            bitPick d₀ d₁ (Bool.not v),
            bitPick e₀ e₁ y} : Set α) ↔
        relabelInput u (middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁) true y
    rw [hset₃ y]
    cases u <;> simp [middlePairRelation, relabelInput, bitPick]

  have hS₄eq :
      middlePairRelation M
          (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
          e₀ e₁ f₀ f₁ =
        relabelInput v (middlePairRelation M d₀ d₁ e₀ e₁ f₀ f₁) := by
    apply eq_of_bijections_of_agree_input_true hS₄
      (relabelInput_bijection v hR₄)
    intro y
    cases v <;> simp [middlePairRelation, relabelInput, bitPick]

  rw [hS₁eq, hS₂eq, hS₃eq, hS₄eq]
  exact (cyclicSatisfiable_four_relabel hR₁ hR₂ hR₃ hR₄ u v).symm

end Rank4ThreePairDual
end HigherRankKUM
