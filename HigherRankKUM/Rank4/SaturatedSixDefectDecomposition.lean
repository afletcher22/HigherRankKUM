import HigherRankKUM.Rank4.SaturatedSixDefectCertification

namespace HigherRankKUM
namespace Rank4SaturatedSixDefectDecomposition

open Set
open scoped Matroid
open Rank4SaturatedSixDefectSchedule
open Rank4SaturatedSixDefectCertification

noncomputable section

variable {α : Type*}

/-- Ambient value formula for an explicit tail position. -/
theorem saturatedFullOrder_tail_value
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α))
    (r : Fin 10) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2) + r.val, by omega⟩ : α) =
      saturatedSlotValue
        (flatOrder.trans (restrictGroundEquiv M H))
        outsideOrder
        (saturatedTailSlot hk r) := by
  rw [saturatedFullOrder_value]
  rw [saturatedIndexEquiv_tail]


/-- Explicit values of the ten-position tail HHHR HR HH RR. -/
@[simp] theorem saturatedFullOrder_tail_H0
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2), by omega⟩ : α) =
      (flatOrder ⟨3 * k - 6, by omega⟩ : α) := by
  have h := saturatedFullOrder_tail_value
    M hk hHsub flatOrder outsideOrder (0 : Fin 10)
  simpa [saturatedTailSlot, saturatedSlotValue] using h

@[simp] theorem saturatedFullOrder_tail_H1
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2) + 1, by omega⟩ : α) =
      (flatOrder ⟨3 * k - 5, by omega⟩ : α) := by
  have h := saturatedFullOrder_tail_value
    M hk hHsub flatOrder outsideOrder (1 : Fin 10)
  simpa [saturatedTailSlot, saturatedSlotValue] using h

@[simp] theorem saturatedFullOrder_tail_H2
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2) + 2, by omega⟩ : α) =
      (flatOrder ⟨3 * k - 4, by omega⟩ : α) := by
  have h := saturatedFullOrder_tail_value
    M hk hHsub flatOrder outsideOrder (2 : Fin 10)
  simpa [saturatedTailSlot, saturatedSlotValue] using h

@[simp] theorem saturatedFullOrder_tail_R3
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2) + 3, by omega⟩ : α) =
      (outsideOrder ⟨k - 2, by omega⟩ : α) := by
  have h := saturatedFullOrder_tail_value
    M hk hHsub flatOrder outsideOrder (3 : Fin 10)
  simpa [saturatedTailSlot, saturatedSlotValue] using h

@[simp] theorem saturatedFullOrder_tail_H4
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2) + 4, by omega⟩ : α) =
      (flatOrder ⟨3 * k - 3, by omega⟩ : α) := by
  have h := saturatedFullOrder_tail_value
    M hk hHsub flatOrder outsideOrder (4 : Fin 10)
  simpa [saturatedTailSlot, saturatedSlotValue] using h

@[simp] theorem saturatedFullOrder_tail_R5
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2) + 5, by omega⟩ : α) =
      (outsideOrder ⟨k - 1, by omega⟩ : α) := by
  have h := saturatedFullOrder_tail_value
    M hk hHsub flatOrder outsideOrder (5 : Fin 10)
  simpa [saturatedTailSlot, saturatedSlotValue] using h

@[simp] theorem saturatedFullOrder_tail_H6
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2) + 6, by omega⟩ : α) =
      (flatOrder ⟨3 * k - 2, by omega⟩ : α) := by
  have h := saturatedFullOrder_tail_value
    M hk hHsub flatOrder outsideOrder (6 : Fin 10)
  simpa [saturatedTailSlot, saturatedSlotValue] using h

@[simp] theorem saturatedFullOrder_tail_H7
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2) + 7, by omega⟩ : α) =
      (flatOrder ⟨3 * k - 1, by omega⟩ : α) := by
  have h := saturatedFullOrder_tail_value
    M hk hHsub flatOrder outsideOrder (7 : Fin 10)
  simpa [saturatedTailSlot, saturatedSlotValue] using h

@[simp] theorem saturatedFullOrder_tail_R8
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2) + 8, by omega⟩ : α) =
      (outsideOrder ⟨k, by omega⟩ : α) := by
  have h := saturatedFullOrder_tail_value
    M hk hHsub flatOrder outsideOrder (8 : Fin 10)
  simpa [saturatedTailSlot, saturatedSlotValue] using h

@[simp] theorem saturatedFullOrder_tail_R9
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder
        ⟨4 * (k - 2) + 9, by omega⟩ : α) =
      (outsideOrder ⟨k + 1, by omega⟩ : α) := by
  have h := saturatedFullOrder_tail_value
    M hk hHsub flatOrder outsideOrder (9 : Fin 10)
  simpa [saturatedTailSlot, saturatedSlotValue] using h

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


/-- Every start before tail offset one has the automatic 3H+1R form.

This is the unbounded regular-region part of the six-defect decomposition. -/
theorem saturated_regular_region_window_decomposition
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α))
    (i : Fin (4 * k + 2))
    (hi : i.val < 4 * (k - 2) + 1) :
    ∃ iH : Fin (3 * k), ∃ iR : Fin (k + 2),
      cyclicWindow 4 (by omega)
          (saturatedFullOrder M hk hHsub flatOrder outsideOrder) i =
        insert (outsideOrder iR : α)
          (cyclicWindow 3 (by omega) flatOrder iH) := by
  let q : Fin (k - 1) := ⟨i.val / 4, by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 4)).2
    have hi' : i.val < 4 * (k - 1) := by omega
    simpa [Nat.mul_comm] using hi'⟩
  have hrem : i.val % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases hr : i.val % 4
  · have hival : i.val = 4 * q.val := by
      dsimp [q]
      have hm := Nat.mod_add_div i.val 4
      omega
    have hiEq : i = ⟨4 * q.val, by omega⟩ := Fin.ext hival
    let iH : Fin (3 * k) := ⟨3 * q.val, by omega⟩
    let iR : Fin (k + 2) := ⟨q.val, by omega⟩
    refine ⟨iH, iR, ?_⟩
    rw [hiEq, cyclicWindow_four_eq]
    have hg1 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val, by omega⟩ : Fin (4 * k + 2)) 1 =
          ⟨4 * q.val + 1, by omega⟩ := by
      simpa using cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val, by omega⟩ : Fin (4 * k + 2)) 1 (by omega)
    have hg2 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val, by omega⟩ : Fin (4 * k + 2)) 2 =
          ⟨4 * q.val + 2, by omega⟩ := by
      simpa using cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val, by omega⟩ : Fin (4 * k + 2)) 2 (by omega)
    have hg3 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val, by omega⟩ : Fin (4 * k + 2)) 3 =
          ⟨4 * q.val + 3, by omega⟩ := by
      simpa using cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val, by omega⟩ : Fin (4 * k + 2)) 3 (by omega)
    rw [hg1, hg2, hg3,
      saturatedFullOrder_regular_H0,
      saturatedFullOrder_regular_H1,
      saturatedFullOrder_regular_H2,
      saturatedFullOrder_regular_R]
    rw [cyclicWindow_three_eq]
    have hh1 :
        cyclicIndex (3 * k) (by omega) iH 1 =
          ⟨3 * q.val + 1, by omega⟩ := by
      dsimp [iH]
      simpa using cyclicIndex_eq_mk_add_of_lt
        (3 * k) (by omega)
        (⟨3 * q.val, by omega⟩ : Fin (3 * k)) 1 (by omega)
    have hh2 :
        cyclicIndex (3 * k) (by omega) iH 2 =
          ⟨3 * q.val + 2, by omega⟩ := by
      dsimp [iH]
      simpa using cyclicIndex_eq_mk_add_of_lt
        (3 * k) (by omega)
        (⟨3 * q.val, by omega⟩ : Fin (3 * k)) 2 (by omega)
    rw [hh1, hh2]
    dsimp [iH, iR]
    ext x
    simp [or_comm, or_left_comm, or_assoc]
  · have hival : i.val = 4 * q.val + 1 := by
      dsimp [q]
      have hm := Nat.mod_add_div i.val 4
      omega
    have hqnext : q.val + 1 < k - 1 := by omega
    let qn : Fin (k - 1) := ⟨q.val + 1, hqnext⟩
    have hiEq : i = ⟨4 * q.val + 1, by omega⟩ := Fin.ext hival
    let iH : Fin (3 * k) := ⟨3 * q.val + 1, by omega⟩
    let iR : Fin (k + 2) := ⟨q.val, by omega⟩
    refine ⟨iH, iR, ?_⟩
    rw [hiEq, cyclicWindow_four_eq]
    have hg1 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val + 1, by omega⟩ : Fin (4 * k + 2)) 1 =
          ⟨4 * q.val + 2, by omega⟩ := by
      simpa using cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val + 1, by omega⟩ : Fin (4 * k + 2)) 1 (by omega)
    have hg2 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val + 1, by omega⟩ : Fin (4 * k + 2)) 2 =
          ⟨4 * q.val + 3, by omega⟩ := by
      simpa using cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val + 1, by omega⟩ : Fin (4 * k + 2)) 2 (by omega)
    have hg3 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val + 1, by omega⟩ : Fin (4 * k + 2)) 3 =
          ⟨4 * qn.val, by omega⟩ := by
      apply Fin.ext
      have h := cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val + 1, by omega⟩ : Fin (4 * k + 2)) 3 (by omega)
      have hv := congrArg Fin.val h
      dsimp [qn] at hv ⊢
      omega
    rw [hg1, hg2, hg3,
      saturatedFullOrder_regular_H1,
      saturatedFullOrder_regular_H2,
      saturatedFullOrder_regular_R,
      saturatedFullOrder_regular_H0]
    rw [cyclicWindow_three_eq]
    have hh1 :
        cyclicIndex (3 * k) (by omega) iH 1 =
          ⟨3 * q.val + 2, by omega⟩ := by
      dsimp [iH]
      simpa using cyclicIndex_eq_mk_add_of_lt
        (3 * k) (by omega)
        (⟨3 * q.val + 1, by omega⟩ : Fin (3 * k)) 1 (by omega)
    have hh2 :
        cyclicIndex (3 * k) (by omega) iH 2 =
          ⟨3 * qn.val, by omega⟩ := by
      apply Fin.ext
      dsimp [iH, qn]
      have h := cyclicIndex_eq_mk_add_of_lt
        (3 * k) (by omega)
        (⟨3 * q.val + 1, by omega⟩ : Fin (3 * k)) 2 (by omega)
      have hv := congrArg Fin.val h
      dsimp at hv ⊢
      omega
    rw [hh1, hh2]
    dsimp [iH, iR, qn]
    ext x
    simp [or_comm, or_left_comm, or_assoc]
  · have hival : i.val = 4 * q.val + 2 := by
      dsimp [q]
      have hm := Nat.mod_add_div i.val 4
      omega
    have hqnext : q.val + 1 < k - 1 := by omega
    let qn : Fin (k - 1) := ⟨q.val + 1, hqnext⟩
    have hiEq : i = ⟨4 * q.val + 2, by omega⟩ := Fin.ext hival
    let iH : Fin (3 * k) := ⟨3 * q.val + 2, by omega⟩
    let iR : Fin (k + 2) := ⟨q.val, by omega⟩
    refine ⟨iH, iR, ?_⟩
    rw [hiEq, cyclicWindow_four_eq]
    have hg1 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val + 2, by omega⟩ : Fin (4 * k + 2)) 1 =
          ⟨4 * q.val + 3, by omega⟩ := by
      simpa using cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val + 2, by omega⟩ : Fin (4 * k + 2)) 1 (by omega)
    have hg2 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val + 2, by omega⟩ : Fin (4 * k + 2)) 2 =
          ⟨4 * qn.val, by omega⟩ := by
      apply Fin.ext
      have h := cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val + 2, by omega⟩ : Fin (4 * k + 2)) 2 (by omega)
      have hv := congrArg Fin.val h
      dsimp [qn] at hv ⊢
      omega
    have hg3 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val + 2, by omega⟩ : Fin (4 * k + 2)) 3 =
          ⟨4 * qn.val + 1, by omega⟩ := by
      apply Fin.ext
      have h := cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val + 2, by omega⟩ : Fin (4 * k + 2)) 3 (by omega)
      have hv := congrArg Fin.val h
      dsimp [qn] at hv ⊢
      omega
    rw [hg1, hg2, hg3,
      saturatedFullOrder_regular_H2,
      saturatedFullOrder_regular_R,
      saturatedFullOrder_regular_H0,
      saturatedFullOrder_regular_H1]
    rw [cyclicWindow_three_eq]
    have hh1 :
        cyclicIndex (3 * k) (by omega) iH 1 =
          ⟨3 * qn.val, by omega⟩ := by
      apply Fin.ext
      dsimp [iH, qn]
      have h := cyclicIndex_eq_mk_add_of_lt
        (3 * k) (by omega)
        (⟨3 * q.val + 2, by omega⟩ : Fin (3 * k)) 1 (by omega)
      have hv := congrArg Fin.val h
      dsimp at hv ⊢
      omega
    have hh2 :
        cyclicIndex (3 * k) (by omega) iH 2 =
          ⟨3 * qn.val + 1, by omega⟩ := by
      apply Fin.ext
      dsimp [iH, qn]
      have h := cyclicIndex_eq_mk_add_of_lt
        (3 * k) (by omega)
        (⟨3 * q.val + 2, by omega⟩ : Fin (3 * k)) 2 (by omega)
      have hv := congrArg Fin.val h
      dsimp at hv ⊢
      omega
    rw [hh1, hh2]
    dsimp [iH, iR, qn]
    ext x
    simp [or_comm, or_left_comm, or_assoc]
  · have hival : i.val = 4 * q.val + 3 := by
      dsimp [q]
      have hm := Nat.mod_add_div i.val 4
      omega
    have hqnext : q.val + 1 < k - 1 := by omega
    let qn : Fin (k - 1) := ⟨q.val + 1, hqnext⟩
    have hiEq : i = ⟨4 * q.val + 3, by omega⟩ := Fin.ext hival
    let iH : Fin (3 * k) := ⟨3 * qn.val, by omega⟩
    let iR : Fin (k + 2) := ⟨q.val, by omega⟩
    refine ⟨iH, iR, ?_⟩
    rw [hiEq, cyclicWindow_four_eq]
    have hg1 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val + 3, by omega⟩ : Fin (4 * k + 2)) 1 =
          ⟨4 * qn.val, by omega⟩ := by
      apply Fin.ext
      have h := cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val + 3, by omega⟩ : Fin (4 * k + 2)) 1 (by omega)
      have hv := congrArg Fin.val h
      dsimp [qn] at hv ⊢
      omega
    have hg2 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val + 3, by omega⟩ : Fin (4 * k + 2)) 2 =
          ⟨4 * qn.val + 1, by omega⟩ := by
      apply Fin.ext
      have h := cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val + 3, by omega⟩ : Fin (4 * k + 2)) 2 (by omega)
      have hv := congrArg Fin.val h
      dsimp [qn] at hv ⊢
      omega
    have hg3 :
        cyclicIndex (4 * k + 2) (by omega)
            (⟨4 * q.val + 3, by omega⟩ : Fin (4 * k + 2)) 3 =
          ⟨4 * qn.val + 2, by omega⟩ := by
      apply Fin.ext
      have h := cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * q.val + 3, by omega⟩ : Fin (4 * k + 2)) 3 (by omega)
      have hv := congrArg Fin.val h
      dsimp [qn] at hv ⊢
      omega
    rw [hg1, hg2, hg3,
      saturatedFullOrder_regular_R,
      saturatedFullOrder_regular_H0,
      saturatedFullOrder_regular_H1,
      saturatedFullOrder_regular_H2]
    rw [cyclicWindow_three_eq]
    have hh1 :
        cyclicIndex (3 * k) (by omega) iH 1 =
          ⟨3 * qn.val + 1, by omega⟩ := by
      dsimp [iH]
      simpa using cyclicIndex_eq_mk_add_of_lt
        (3 * k) (by omega)
        (⟨3 * qn.val, by omega⟩ : Fin (3 * k)) 1 (by omega)
    have hh2 :
        cyclicIndex (3 * k) (by omega) iH 2 =
          ⟨3 * qn.val + 2, by omega⟩ := by
      dsimp [iH]
      simpa using cyclicIndex_eq_mk_add_of_lt
        (3 * k) (by omega)
        (⟨3 * qn.val, by omega⟩ : Fin (3 * k)) 2 (by omega)
    rw [hh1, hh2]
    dsimp [iH, iR, qn]
    ext x
    simp [or_comm, or_left_comm, or_assoc]


/-- Nondefect tail start p+1 has the automatic 3H+1R form. -/
theorem saturated_tail_p1_window_decomposition
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    cyclicWindow 4 (by omega)
        (saturatedFullOrder M hk hHsub flatOrder outsideOrder)
        ⟨4 * (k - 2) + 1, by omega⟩ =
      insert (outsideOrder ⟨k - 2, by omega⟩ : α)
        (cyclicWindow 3 (by omega) flatOrder
          ⟨3 * k - 5, by omega⟩) := by
  let i : Fin (4 * k + 2) := ⟨4 * (k - 2) + 1, by omega⟩
  rw [cyclicWindow_four_eq]
  have g1 : cyclicIndex (4 * k + 2) (by omega) i 1 =
      ⟨4 * (k - 2) + 2, by omega⟩ := by
    dsimp [i]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (4 * k + 2) (by omega) i 1 (by omega)
  have g2 : cyclicIndex (4 * k + 2) (by omega) i 2 =
      ⟨4 * (k - 2) + 3, by omega⟩ := by
    dsimp [i]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (4 * k + 2) (by omega) i 2 (by omega)
  have g3 : cyclicIndex (4 * k + 2) (by omega) i 3 =
      ⟨4 * (k - 2) + 4, by omega⟩ := by
    dsimp [i]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (4 * k + 2) (by omega) i 3 (by omega)
  rw [g1, g2, g3,
    saturatedFullOrder_tail_H1,
    saturatedFullOrder_tail_H2,
    saturatedFullOrder_tail_R3,
    saturatedFullOrder_tail_H4]
  rw [cyclicWindow_three_eq]
  let iH : Fin (3 * k) := ⟨3 * k - 5, by omega⟩
  have h1 : cyclicIndex (3 * k) (by omega) iH 1 =
      ⟨3 * k - 4, by omega⟩ := by
    dsimp [iH]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (3 * k) (by omega) iH 1 (by omega)
  have h2 : cyclicIndex (3 * k) (by omega) iH 2 =
      ⟨3 * k - 3, by omega⟩ := by
    dsimp [iH]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (3 * k) (by omega) iH 2 (by omega)
  rw [h1, h2]
  dsimp [i, iH]
  ext x
  simp [or_comm, or_left_comm, or_assoc]

/-- Nondefect tail start p+4 has the automatic 3H+1R form. -/
theorem saturated_tail_p4_window_decomposition
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    cyclicWindow 4 (by omega)
        (saturatedFullOrder M hk hHsub flatOrder outsideOrder)
        ⟨4 * (k - 2) + 4, by omega⟩ =
      insert (outsideOrder ⟨k - 1, by omega⟩ : α)
        (cyclicWindow 3 (by omega) flatOrder
          ⟨3 * k - 3, by omega⟩) := by
  let i : Fin (4 * k + 2) := ⟨4 * (k - 2) + 4, by omega⟩
  rw [cyclicWindow_four_eq]
  have g1 : cyclicIndex (4 * k + 2) (by omega) i 1 =
      ⟨4 * (k - 2) + 5, by omega⟩ := by
    dsimp [i]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (4 * k + 2) (by omega) i 1 (by omega)
  have g2 : cyclicIndex (4 * k + 2) (by omega) i 2 =
      ⟨4 * (k - 2) + 6, by omega⟩ := by
    dsimp [i]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (4 * k + 2) (by omega) i 2 (by omega)
  have g3 : cyclicIndex (4 * k + 2) (by omega) i 3 =
      ⟨4 * (k - 2) + 7, by omega⟩ := by
    dsimp [i]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (4 * k + 2) (by omega) i 3 (by omega)
  rw [g1, g2, g3,
    saturatedFullOrder_tail_H4,
    saturatedFullOrder_tail_R5,
    saturatedFullOrder_tail_H6,
    saturatedFullOrder_tail_H7]
  rw [cyclicWindow_three_eq]
  let iH : Fin (3 * k) := ⟨3 * k - 3, by omega⟩
  have h1 : cyclicIndex (3 * k) (by omega) iH 1 =
      ⟨3 * k - 2, by omega⟩ := by
    dsimp [iH]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (3 * k) (by omega) iH 1 (by omega)
  have h2 : cyclicIndex (3 * k) (by omega) iH 2 =
      ⟨3 * k - 1, by omega⟩ := by
    dsimp [iH]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (3 * k) (by omega) iH 2 (by omega)
  rw [h1, h2]
  dsimp [i, iH]
  ext x
  simp [or_comm, or_left_comm, or_assoc]

/-- The wraparound nondefect start p+9 has the automatic 3H+1R form. -/
theorem saturated_tail_p9_window_decomposition
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α)) :
    cyclicWindow 4 (by omega)
        (saturatedFullOrder M hk hHsub flatOrder outsideOrder)
        ⟨4 * (k - 2) + 9, by omega⟩ =
      insert (outsideOrder ⟨k + 1, by omega⟩ : α)
        (cyclicWindow 3 (by omega) flatOrder ⟨0, by omega⟩) := by
  let i : Fin (4 * k + 2) := ⟨4 * (k - 2) + 9, by omega⟩
  rw [cyclicWindow_four_eq]
  have g1 : cyclicIndex (4 * k + 2) (by omega) i 1 =
      ⟨0, by omega⟩ := by
    apply Fin.ext
    have h := cyclicIndex_eq_mk_sub_of_ge_of_lt_two_mul
      (4 * k + 2) (by omega) i 1 (by omega) (by omega)
    have hv := congrArg Fin.val h
    dsimp [i] at hv ⊢
    omega
  have g2 : cyclicIndex (4 * k + 2) (by omega) i 2 =
      ⟨1, by omega⟩ := by
    apply Fin.ext
    have h := cyclicIndex_eq_mk_sub_of_ge_of_lt_two_mul
      (4 * k + 2) (by omega) i 2 (by omega) (by omega)
    have hv := congrArg Fin.val h
    dsimp [i] at hv ⊢
    omega
  have g3 : cyclicIndex (4 * k + 2) (by omega) i 3 =
      ⟨2, by omega⟩ := by
    apply Fin.ext
    have h := cyclicIndex_eq_mk_sub_of_ge_of_lt_two_mul
      (4 * k + 2) (by omega) i 3 (by omega) (by omega)
    have hv := congrArg Fin.val h
    dsimp [i] at hv ⊢
    omega
  let q0 : Fin (k - 1) := ⟨0, by omega⟩
  have h0 :
      (saturatedFullOrder M hk hHsub flatOrder outsideOrder
          ⟨0, by omega⟩ : α) = (flatOrder ⟨0, by omega⟩ : α) := by
    simpa [q0] using
      (saturatedFullOrder_regular_H0
        M hk hHsub flatOrder outsideOrder q0)
  have h1v :
      (saturatedFullOrder M hk hHsub flatOrder outsideOrder
          ⟨1, by omega⟩ : α) = (flatOrder ⟨1, by omega⟩ : α) := by
    simpa [q0] using
      (saturatedFullOrder_regular_H1
        M hk hHsub flatOrder outsideOrder q0)
  have h2v :
      (saturatedFullOrder M hk hHsub flatOrder outsideOrder
          ⟨2, by omega⟩ : α) = (flatOrder ⟨2, by omega⟩ : α) := by
    simpa [q0] using
      (saturatedFullOrder_regular_H2
        M hk hHsub flatOrder outsideOrder q0)
  rw [g1, g2, g3, saturatedFullOrder_tail_R9, h0, h1v, h2v]
  rw [cyclicWindow_three_eq]
  let iH : Fin (3 * k) := ⟨0, by omega⟩
  have hh1 : cyclicIndex (3 * k) (by omega) iH 1 =
      ⟨1, by omega⟩ := by
    dsimp [iH]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (3 * k) (by omega) iH 1 (by omega)
  have hh2 : cyclicIndex (3 * k) (by omega) iH 2 =
      ⟨2, by omega⟩ := by
    dsimp [iH]
    simpa using cyclicIndex_eq_mk_add_of_lt
      (3 * k) (by omega) iH 2 (by omega)
  rw [hh1, hh2]
  dsimp [i, iH]
  ext x
  simp [or_comm, or_left_comm, or_assoc]

/-- Full nondefect decomposition for the explicit saturated schedule.

For every start outside the six named defect starts, the rank-four window is
one complement element plus one cyclic rank-three window of the flat order. -/
theorem saturated_nondefect_window_decomposition
    (M : Matroid α) {H : Set α} {k : ℕ}
    (hk : 2 ≤ k) (hHsub : H ⊆ M.E)
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α))
    (i : Fin (4 * k + 2))
    (hi : i ∉ saturatedDefectStarts k hk) :
    ∃ iH : Fin (3 * k), ∃ iR : Fin (k + 2),
      cyclicWindow 4 (by omega)
          (saturatedFullOrder M hk hHsub flatOrder outsideOrder) i =
        insert (outsideOrder iR : α)
          (cyclicWindow 3 (by omega) flatOrder iH) := by
  by_cases hreg : i.val < 4 * (k - 2) + 1
  · exact saturated_regular_region_window_decomposition
      M hk hHsub flatOrder outsideOrder i hreg
  have hn2 : i.val ≠ 4 * (k - 2) + 2 := by
    intro hv
    apply hi
    simp [saturatedDefectStarts, Fin.ext_iff, hv]
  have hn3 : i.val ≠ 4 * (k - 2) + 3 := by
    intro hv
    apply hi
    simp [saturatedDefectStarts, Fin.ext_iff, hv]
  have hn5 : i.val ≠ 4 * (k - 2) + 5 := by
    intro hv
    apply hi
    simp [saturatedDefectStarts, Fin.ext_iff, hv]
  have hn6 : i.val ≠ 4 * (k - 2) + 6 := by
    intro hv
    apply hi
    simp [saturatedDefectStarts, Fin.ext_iff, hv]
  have hn7 : i.val ≠ 4 * (k - 2) + 7 := by
    intro hv
    apply hi
    simp [saturatedDefectStarts, Fin.ext_iff, hv]
  have hn8 : i.val ≠ 4 * (k - 2) + 8 := by
    intro hv
    apply hi
    simp [saturatedDefectStarts, Fin.ext_iff, hv]
  have hcases :
      i.val = 4 * (k - 2) + 1 ∨
      i.val = 4 * (k - 2) + 4 ∨
      i.val = 4 * (k - 2) + 9 := by
    omega
  rcases hcases with h1 | h4 | h9
  · have hiEq :
        i = ⟨4 * (k - 2) + 1, by omega⟩ := by
      apply Fin.ext
      exact h1
    rw [hiEq]
    exact ⟨⟨3 * k - 5, by omega⟩, ⟨k - 2, by omega⟩,
      saturated_tail_p1_window_decomposition
        M hk hHsub flatOrder outsideOrder⟩
  · have hiEq :
        i = ⟨4 * (k - 2) + 4, by omega⟩ := by
      apply Fin.ext
      exact h4
    rw [hiEq]
    exact ⟨⟨3 * k - 3, by omega⟩, ⟨k - 1, by omega⟩,
      saturated_tail_p4_window_decomposition
        M hk hHsub flatOrder outsideOrder⟩
  · have hiEq :
        i = ⟨4 * (k - 2) + 9, by omega⟩ := by
      apply Fin.ext
      exact h9
    rw [hiEq]
    exact ⟨⟨0, by omega⟩, ⟨k + 1, by omega⟩,
      saturated_tail_p9_window_decomposition
        M hk hHsub flatOrder outsideOrder⟩


/-- Concrete six-defect certification for the explicit saturated full order.

Once the flat order is a rank-three CBO, all nondefect windows of the explicit
schedule are automatic. Thus the full order is a rank-four CBO as soon as the
six named 2H+2R defect windows are bases. -/
theorem cyclicBasisOrder_saturatedFullOrder_of_six_defect_bases
    {M : Matroid α} {H : Set α} {k : ℕ}
    (hk : 2 ≤ k)
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hHsub : H ⊆ M.E)
    (hHflat : M.IsFlat H)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (flatOrder : Fin (3 * k) ≃ (M ↾ H).E)
    (outsideOrder : Fin (k + 2) ≃ (M.E \ H : Set α))
    (hFlatCBO :
      CyclicBasisOrder (M ↾ H) 3 (by omega) flatOrder)
    (h2 :
      M.IsBase (cyclicWindow 4 (by omega)
        (saturatedFullOrder M hk hHsub flatOrder outsideOrder)
        ⟨4 * (k - 2) + 2, by omega⟩))
    (h3 :
      M.IsBase (cyclicWindow 4 (by omega)
        (saturatedFullOrder M hk hHsub flatOrder outsideOrder)
        ⟨4 * (k - 2) + 3, by omega⟩))
    (h5 :
      M.IsBase (cyclicWindow 4 (by omega)
        (saturatedFullOrder M hk hHsub flatOrder outsideOrder)
        ⟨4 * (k - 2) + 5, by omega⟩))
    (h6 :
      M.IsBase (cyclicWindow 4 (by omega)
        (saturatedFullOrder M hk hHsub flatOrder outsideOrder)
        ⟨4 * (k - 2) + 6, by omega⟩))
    (h7 :
      M.IsBase (cyclicWindow 4 (by omega)
        (saturatedFullOrder M hk hHsub flatOrder outsideOrder)
        ⟨4 * (k - 2) + 7, by omega⟩))
    (h8 :
      M.IsBase (cyclicWindow 4 (by omega)
        (saturatedFullOrder M hk hHsub flatOrder outsideOrder)
        ⟨4 * (k - 2) + 8, by omega⟩)) :
    CyclicBasisOrder M 4 (by omega)
      (saturatedFullOrder M hk hHsub flatOrder outsideOrder) := by
  apply cyclicBasisOrder_of_saturated_six_defect_decomposition
    hk hGroundFin hRank hHsub hHflat hHrank
    flatOrder outsideOrder
    (saturatedFullOrder M hk hHsub flatOrder outsideOrder)
    hFlatCBO
  · intro i hi
    exact saturated_nondefect_window_decomposition
      M hk hHsub flatOrder outsideOrder i hi
  · exact h2
  · exact h3
  · exact h5
  · exact h6
  · exact h7
  · exact h8

end

end Rank4SaturatedSixDefectDecomposition
end HigherRankKUM
