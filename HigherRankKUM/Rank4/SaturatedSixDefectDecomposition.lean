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

end

end Rank4SaturatedSixDefectDecomposition
end HigherRankKUM
