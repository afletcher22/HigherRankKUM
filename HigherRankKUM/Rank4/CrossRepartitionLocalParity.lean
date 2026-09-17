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

/-- Representation-free cross-repartition parity in the exact left-label
convention used by rank-four `localRelation`.

The generic six-block theorem uses `T(X,Y,Z)` with the natural order on `X`.
The actual admissible-pair-cycle relation uses the reversed left pair, hence
`T(X^rev,Y,Z)`.  If all eight affected local relations are forced, reversing
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
  let R₁ := middlePairRelation M a₀ a₁ b₀ b₁ c₀ c₁
  let R₂ := middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁
  let R₃ := middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁
  let R₄ := middlePairRelation M d₀ d₁ e₀ e₁ f₀ f₁
  let S₁ := middlePairRelation M a₀ a₁ b₀ b₁
    (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
  let S₂ := middlePairRelation M b₀ b₁
    (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
    (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
  let S₃ := middlePairRelation M
    (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
    (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
    e₀ e₁
  let S₄ := middlePairRelation M
    (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
    e₀ e₁ f₀ f₁
  have hR₁nat : BijectionRelation R₁ :=
    (relabelInput_bijection_iff true).1 (by
      simpa [R₁, middlePairRelation_swap_left_eq_relabelInput_true] using hR₁)
  have hR₂nat : BijectionRelation R₂ :=
    (relabelInput_bijection_iff true).1 (by
      simpa [R₂, middlePairRelation_swap_left_eq_relabelInput_true] using hR₂)
  have hR₃nat : BijectionRelation R₃ :=
    (relabelInput_bijection_iff true).1 (by
      simpa [R₃, middlePairRelation_swap_left_eq_relabelInput_true] using hR₃)
  have hR₄nat : BijectionRelation R₄ :=
    (relabelInput_bijection_iff true).1 (by
      simpa [R₄, middlePairRelation_swap_left_eq_relabelInput_true] using hR₄)
  have hS₁nat : BijectionRelation S₁ :=
    (relabelInput_bijection_iff true).1 (by
      simpa [S₁, middlePairRelation_swap_left_eq_relabelInput_true] using hS₁)
  have hS₂nat : BijectionRelation S₂ :=
    (relabelInput_bijection_iff true).1 (by
      simpa [S₂, middlePairRelation_swap_left_eq_relabelInput_true] using hS₂)
  have hS₃nat : BijectionRelation S₃ :=
    (relabelInput_bijection_iff true).1 (by
      have hswap := middlePairRelation_swap_left_eq_relabelInput_true M
        (bitPick c₀ c₁ u) (bitPick d₀ d₁ v)
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v)) e₀ e₁
      simpa [S₃] using (show BijectionRelation (relabelInput true S₃) from by
        rw [← hswap]
        exact hS₃))
  have hS₄nat : BijectionRelation S₄ :=
    (relabelInput_bijection_iff true).1 (by
      have hswap := middlePairRelation_swap_left_eq_relabelInput_true M
        (bitPick c₀ c₁ (Bool.not u)) (bitPick d₀ d₁ (Bool.not v))
        e₀ e₁ f₀ f₁
      simpa [S₄] using (show BijectionRelation (relabelInput true S₄) from by
        rw [← hswap]
        exact hS₄))
  have hcross := crossRepartition_middlePairRelations_preserve_cyclicSatisfiable M
    u v hR₁nat hR₂nat hR₃nat hR₄nat hS₁nat hS₂nat hS₃nat hS₄nat
  have holdFlip := cyclicSatisfiable_four_relabelInput_true
    hR₁nat hR₂nat hR₃nat hR₄nat
  have hnewFlip := cyclicSatisfiable_four_relabelInput_true
    hS₁nat hS₂nat hS₃nat hS₄nat
  rw [middlePairRelation_swap_left_eq_relabelInput_true,
    middlePairRelation_swap_left_eq_relabelInput_true,
    middlePairRelation_swap_left_eq_relabelInput_true,
    middlePairRelation_swap_left_eq_relabelInput_true]
  change CyclicSatisfiable
      [relabelInput true R₁, relabelInput true R₂,
        relabelInput true R₃, relabelInput true R₄] ↔ _
  have hright :
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
          e₀ e₁ f₀ f₁] ↔
        CyclicSatisfiable
          [relabelInput true S₁, relabelInput true S₂,
            relabelInput true S₃, relabelInput true S₄] := by
    simp only [S₁, S₂, S₃, S₄]
    rw [← middlePairRelation_swap_left_eq_relabelInput_true,
      ← middlePairRelation_swap_left_eq_relabelInput_true,
      ← middlePairRelation_swap_left_eq_relabelInput_true,
      ← middlePairRelation_swap_left_eq_relabelInput_true]
  rw [hright]
  exact holdFlip.trans (hcross.trans hnewFlip.symm)

end Rank4ThreePairDual
end HigherRankKUM
