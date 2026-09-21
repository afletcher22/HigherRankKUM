import HigherRankKUM.Rank4.CrossRepartitionParity
import HigherRankKUM.Rank4.MiddlePairRelabel

namespace HigherRankKUM
namespace Rank4ThreePairDual

open BinaryRelationCycle
open PairCycle

variable {α : Type*}

/-- Reversing the two labels on the left endpoint pair is exactly the input
flip used by `AdmissiblePairCycle.localRelation`. -/
theorem middlePairRelation_swap_left_eq_relabelInput_true
    (M : Matroid α) (x₀ x₁ y₀ y₁ z₀ z₁ : α) :
    middlePairRelation M x₁ x₀ y₀ y₁ z₀ z₁ =
      relabelInput true (middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁) := by
  simpa [bitPick] using
    middlePairRelation_relabel_left M x₀ x₁ y₀ y₁ z₀ z₁ true

/-- Reversing the left endpoint labels preserves forcedness exactly. -/
theorem middlePairRelation_swap_left_bijection_iff
    (M : Matroid α) (x₀ x₁ y₀ y₁ z₀ z₁ : α) :
    BijectionRelation (middlePairRelation M x₁ x₀ y₀ y₁ z₀ z₁) ↔
      BijectionRelation (middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁) := by
  rw [middlePairRelation_swap_left_eq_relabelInput_true,
    relabelInput_bijection_iff]

/-- Representation-free cross-repartition parity in the exact left-label
convention used by rank-four `localRelation`.

The generic six-block theorem uses `T(X,Y,Z)` with the natural order on `X`.
The actual admissible-pair-cycle relation uses the reversed left pair, hence
`T(X^rev,Y,Z)`. If all eight affected local relations are forced, reversing
the left endpoint in all four old relations and all four new relations does
not change the parity comparison. -/
theorem crossRepartition_localRelations_preserve_cyclicSatisfiable
    (M : Matroid α)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ e₀ e₁ f₀ f₁ : α}
    (u v : Bool)
    (hR₁ : BijectionRelation (middlePairRelation M a₁ a₀ b₀ b₁ c₀ c₁))
    (hR₂ : BijectionRelation (middlePairRelation M b₁ b₀ c₀ c₁ d₀ d₁))
    (hR₃ : BijectionRelation (middlePairRelation M c₁ c₀ d₀ d₁ e₀ e₁))
    (hR₄ : BijectionRelation (middlePairRelation M d₁ d₀ e₀ e₁ f₀ f₁))
    (hS₁ : BijectionRelation
      (middlePairRelation M a₁ a₀ b₀ b₁
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)))
    (hS₂ : BijectionRelation
      (middlePairRelation M b₁ b₀
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))))
    (hS₃ : BijectionRelation
      (middlePairRelation M
        (bitPick d₀ d₁ v) (bitPick c₀ c₁ u)
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
        e₀ e₁))
    (hS₄ : BijectionRelation
      (middlePairRelation M
        (bitPick d₀ d₁ (Bool.not v)) (bitPick c₀ c₁ (Bool.not u))
        e₀ e₁ f₀ f₁)) :
    CyclicSatisfiable
      [middlePairRelation M a₁ a₀ b₀ b₁ c₀ c₁,
       middlePairRelation M b₁ b₀ c₀ c₁ d₀ d₁,
       middlePairRelation M c₁ c₀ d₀ d₁ e₀ e₁,
       middlePairRelation M d₁ d₀ e₀ e₁ f₀ f₁] ↔
    CyclicSatisfiable
      [middlePairRelation M a₁ a₀ b₀ b₁
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v),
       middlePairRelation M b₁ b₀
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v)),
       middlePairRelation M
        (bitPick d₀ d₁ v) (bitPick c₀ c₁ u)
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
        e₀ e₁,
       middlePairRelation M
        (bitPick d₀ d₁ (Bool.not v)) (bitPick c₀ c₁ (Bool.not u))
        e₀ e₁ f₀ f₁] := by
  have hR₁nat := (middlePairRelation_swap_left_bijection_iff
    M a₀ a₁ b₀ b₁ c₀ c₁).1 hR₁
  have hR₂nat := (middlePairRelation_swap_left_bijection_iff
    M b₀ b₁ c₀ c₁ d₀ d₁).1 hR₂
  have hR₃nat := (middlePairRelation_swap_left_bijection_iff
    M c₀ c₁ d₀ d₁ e₀ e₁).1 hR₃
  have hR₄nat := (middlePairRelation_swap_left_bijection_iff
    M d₀ d₁ e₀ e₁ f₀ f₁).1 hR₄
  have hS₁nat := (middlePairRelation_swap_left_bijection_iff
    M a₀ a₁ b₀ b₁
      (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)).1 hS₁
  have hS₂nat := (middlePairRelation_swap_left_bijection_iff
    M b₀ b₁
      (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
      (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))).1 hS₂
  have hS₃nat := (middlePairRelation_swap_left_bijection_iff
    M
      (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
      (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
      e₀ e₁).1 hS₃
  have hS₄nat := (middlePairRelation_swap_left_bijection_iff
    M
      (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
      e₀ e₁ f₀ f₁).1 hS₄
  have hcross := crossRepartition_middlePairRelations_preserve_cyclicSatisfiable M
    u v hR₁nat hR₂nat hR₃nat hR₄nat hS₁nat hS₂nat hS₃nat hS₄nat
  calc
    CyclicSatisfiable
        [middlePairRelation M a₁ a₀ b₀ b₁ c₀ c₁,
         middlePairRelation M b₁ b₀ c₀ c₁ d₀ d₁,
         middlePairRelation M c₁ c₀ d₀ d₁ e₀ e₁,
         middlePairRelation M d₁ d₀ e₀ e₁ f₀ f₁] ↔
      CyclicSatisfiable
        [middlePairRelation M a₀ a₁ b₀ b₁ c₀ c₁,
         middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁,
         middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁,
         middlePairRelation M d₀ d₁ e₀ e₁ f₀ f₁] := by
          rw [
            middlePairRelation_swap_left_eq_relabelInput_true
              M a₀ a₁ b₀ b₁ c₀ c₁,
            middlePairRelation_swap_left_eq_relabelInput_true
              M b₀ b₁ c₀ c₁ d₀ d₁,
            middlePairRelation_swap_left_eq_relabelInput_true
              M c₀ c₁ d₀ d₁ e₀ e₁,
            middlePairRelation_swap_left_eq_relabelInput_true
              M d₀ d₁ e₀ e₁ f₀ f₁]
          exact cyclicSatisfiable_four_relabelInput_true
            hR₁nat hR₂nat hR₃nat hR₄nat
    _ ↔ CyclicSatisfiable
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
          e₀ e₁ f₀ f₁] := hcross
    _ ↔ CyclicSatisfiable
        [middlePairRelation M a₁ a₀ b₀ b₁
          (bitPick c₀ c₁ u) (bitPick d₀ d₁ v),
         middlePairRelation M b₁ b₀
          (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
          (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v)),
         middlePairRelation M
          (bitPick d₀ d₁ v) (bitPick c₀ c₁ u)
          (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
          e₀ e₁,
         middlePairRelation M
          (bitPick d₀ d₁ (Bool.not v)) (bitPick c₀ c₁ (Bool.not u))
          e₀ e₁ f₀ f₁] := by
          rw [
            middlePairRelation_swap_left_eq_relabelInput_true
              M a₀ a₁ b₀ b₁
                (bitPick c₀ c₁ u) (bitPick d₀ d₁ v),
            middlePairRelation_swap_left_eq_relabelInput_true
              M b₀ b₁
                (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
                (bitPick c₀ c₁ (Bool.not u))
                (bitPick d₀ d₁ (Bool.not v)),
            middlePairRelation_swap_left_eq_relabelInput_true
              M (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
                (bitPick c₀ c₁ (Bool.not u))
                (bitPick d₀ d₁ (Bool.not v)) e₀ e₁,
            middlePairRelation_swap_left_eq_relabelInput_true
              M (bitPick c₀ c₁ (Bool.not u))
                (bitPick d₀ d₁ (Bool.not v)) e₀ e₁ f₀ f₁]
          exact (cyclicSatisfiable_four_relabelInput_true
            hS₁nat hS₂nat hS₃nat hS₄nat).symm

end Rank4ThreePairDual
end HigherRankKUM
