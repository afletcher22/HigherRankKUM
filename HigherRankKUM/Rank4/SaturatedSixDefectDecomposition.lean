import HigherRankKUM.Rank4.SaturatedSixDefectCertification

namespace HigherRankKUM
namespace Rank4SaturatedSixDefectDecomposition

open Set
open scoped Matroid
open Rank4SaturatedSixDefectSchedule
open Rank4SaturatedSixDefectCertification

noncomputable section

variable {α : Type*}

@[simp] theorem saturatedFullOrder_regular_H0
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α))
    (q : Fin (k - 1)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * q.val, by omega⟩ : α) =
      (flatOrder ⟨3 * q.val, by omega⟩ : α) := by
  have h :=
    saturatedFullOrder_regular_block_value
      M hk hHsub flatOrder outsideOrder q (0 : Fin 4)
  simpa [saturatedRegularBlockSlot, saturatedSlotValue] using h

@[simp] theorem saturatedFullOrder_regular_H1
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α))
    (q : Fin (k - 1)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * q.val + 1, by omega⟩ : α) =
      (flatOrder ⟨3 * q.val + 1, by omega⟩ : α) := by
  have h :=
    saturatedFullOrder_regular_block_value
      M hk hHsub flatOrder outsideOrder q (1 : Fin 4)
  simpa [saturatedRegularBlockSlot, saturatedSlotValue, Nat.add_comm] using h

@[simp] theorem saturatedFullOrder_regular_H2
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α))
    (q : Fin (k - 1)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * q.val + 2, by omega⟩ : α) =
      (flatOrder ⟨3 * q.val + 2, by omega⟩ : α) := by
  have h :=
    saturatedFullOrder_regular_block_value
      M hk hHsub flatOrder outsideOrder q (2 : Fin 4)
  simpa [saturatedRegularBlockSlot, saturatedSlotValue, Nat.add_comm] using h

@[simp] theorem saturatedFullOrder_regular_R
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α))
    (q : Fin (k - 1)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * q.val + 3, by omega⟩ : α) =
      (outsideOrder ⟨q.val, by omega⟩ : α) := by
  have h :=
    saturatedFullOrder_regular_block_value
      M hk hHsub flatOrder outsideOrder q (3 : Fin 4)
  simpa [saturatedRegularBlockSlot, saturatedSlotValue, Nat.add_comm] using h

end

end Rank4SaturatedSixDefectDecomposition
end HigherRankKUM
