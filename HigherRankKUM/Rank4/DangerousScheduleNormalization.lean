import HigherRankKUM.Rank4.DangerousScheduleSymbolic
import HigherRankKUM.Rank4.CyclicIndexArithmetic
import HigherRankKUM.CyclicRotation
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- Rotate a core CBO so a chosen source index appears at a chosen target
index. The returned pointwise identity tracks every later cyclic offset. -/
theorem exists_shifted_cbo_with_start
    {M : Matroid α} {n r : ℕ}
    (hn : 0 < n)
    (order : Fin n ≃ M.E)
    (hOrder : CyclicBasisOrder M r hn order)
    (src target : Fin n) :
    ∃ order' : Fin n ≃ M.E,
      CyclicBasisOrder M r hn order' ∧
      ∀ j : ℕ,
        (order' (cyclicIndex n hn target j) : α) =
          (order (cyclicIndex n hn src j) : α) := by
  obtain ⟨t, ht, _⟩ :=
    existsUnique_cyclicIndex_offset n hn target src
  let order' : Fin n ≃ M.E :=
    (cyclicShiftEquiv n hn t.val).trans order
  have hCBO : CyclicBasisOrder M r hn order' :=
    hOrder.shift hn order t.val
  refine ⟨order', hCBO, ?_⟩
  intro j
  change
    (order
      (cyclicShiftEquiv n hn t.val
        (cyclicIndex n hn target j)) : α) =
      (order (cyclicIndex n hn src j) : α)
  rw [cyclicShiftEquiv_cyclicIndex, cyclicShiftEquiv_apply, ← ht]

/-- Rotate adjacent good edges so they become the two wrap-adjacent core
edges at indices 3k-1 and 3k. -/
theorem exists_shifted_adjacent_good_at_end
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (i : Fin (3 * k + 1))
    (hgood0 : DangerousHyperplaneEdgeGood order i)
    (hgood1 :
      DangerousHyperplaneEdgeGood order
        (cyclicIndex (3 * k + 1) (by omega) i 1)) :
    ∃ order' : Fin (3 * k + 1) ≃ (M.restrict H).E,
      CyclicBasisOrder (M.restrict H) 3 (by omega) order' ∧
      DangerousHyperplaneEdgeGood order'
        ⟨3 * k - 1, by omega⟩ ∧
      DangerousHyperplaneEdgeGood order'
        ⟨3 * k, by omega⟩ := by
  let n := 3 * k + 1
  let hn : 0 < n := by
    dsimp [n]
    omega
  let target : Fin n := ⟨3 * k - 1, by omega⟩
  obtain ⟨order', hOrder', hmap⟩ :=
    exists_shifted_cbo_with_start hn order hOrder i target
  have hmap0 :
      (order' target : α) = (order i : α) := by
    simpa [target, n, hn] using hmap 0
  have hmap1 :
      (order' (cyclicIndex n hn target 1) : α) =
        (order (cyclicIndex n hn i 1) : α) :=
    hmap 1
  have hmap2 :
      (order' (cyclicIndex n hn target 2) : α) =
        (order (cyclicIndex n hn i 2) : α) :=
    hmap 2

  have ht1 :
      cyclicIndex n hn target 1 = ⟨3 * k, by omega⟩ := by
    have h :=
      cyclicIndex_eq_mk_add_of_lt n hn target 1 (by
        dsimp [target, n]
        omega)
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [target, n] at hv ⊢
    omega
  have ht2 :
      cyclicIndex n hn target 2 = ⟨0, by omega⟩ := by
    have h :=
      cyclicIndex_eq_mk_sub_of_ge_of_lt_two_mul n hn target 2
        (by dsimp [target, n]; omega)
        (by dsimp [target, n]; omega)
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [target, n] at hv ⊢
    omega

  have hgoodEnd :
      DangerousHyperplaneEdgeGood order'
        ⟨3 * k - 1, by omega⟩ := by
    unfold DangerousHyperplaneEdgeGood at hgood0 ⊢
    rw [show (⟨3 * k - 1, by omega⟩ : Fin n) = target by rfl,
      ht1, hmap0]
    have hmap1' :
        (order' ⟨3 * k, by omega⟩ : α) =
          (order (cyclicIndex n hn i 1) : α) := by
      rw [← ht1]
      exact hmap1
    rw [hmap1']
    simpa [n, hn] using hgood0

  have hgoodWrap :
      DangerousHyperplaneEdgeGood order'
        ⟨3 * k, by omega⟩ := by
    unfold DangerousHyperplaneEdgeGood at hgood1 ⊢
    have hnext :
        cyclicIndex n hn (⟨3 * k, by omega⟩ : Fin n) 1 =
          ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [cyclicIndex, n]
    rw [hnext]
    have hmap1' :
        (order' ⟨3 * k, by omega⟩ : α) =
          (order (cyclicIndex n hn i 1) : α) := by
      rw [← ht1]
      exact hmap1
    have hmap2' :
        (order' ⟨0, by omega⟩ : α) =
          (order (cyclicIndex n hn i 2) : α) := by
      rw [← ht2]
      exact hmap2
    rw [hmap1', hmap2']
    have hadd :
        cyclicIndex n hn
            (cyclicIndex n hn i 1) 1 =
          cyclicIndex n hn i 2 := by
      rw [cyclicIndex_add]
    simpa [n, hn, hadd] using hgood1

  exact ⟨order', hOrder', hgoodEnd, hgoodWrap⟩

/-- Rotate distance-two good edges so they become the core edges at
indices 0 and 2. -/
theorem exists_shifted_distance_two_good_at_start
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (i : Fin (3 * k + 1))
    (hgood0 : DangerousHyperplaneEdgeGood order i)
    (hgood2 :
      DangerousHyperplaneEdgeGood order
        (cyclicIndex (3 * k + 1) (by omega) i 2)) :
    ∃ order' : Fin (3 * k + 1) ≃ (M.restrict H).E,
      CyclicBasisOrder (M.restrict H) 3 (by omega) order' ∧
      DangerousHyperplaneEdgeGood order' ⟨0, by omega⟩ ∧
      DangerousHyperplaneEdgeGood order' ⟨2, by omega⟩ := by
  let n := 3 * k + 1
  let hn : 0 < n := by
    dsimp [n]
    omega
  let target : Fin n := ⟨0, by omega⟩
  obtain ⟨order', hOrder', hmap⟩ :=
    exists_shifted_cbo_with_start hn order hOrder i target

  have hmap0 :
      (order' ⟨0, by omega⟩ : α) = (order i : α) := by
    simpa [target, n, hn] using hmap 0
  have hmap1 :
      (order' ⟨1, by omega⟩ : α) =
        (order (cyclicIndex n hn i 1) : α) := by
    have h := hmap 1
    have ht :
        cyclicIndex n hn target 1 = ⟨1, by omega⟩ := by
      have h :=
        cyclicIndex_eq_mk_add_of_lt n hn target 1 (by
          dsimp [target, n]
          omega)
      apply Fin.ext
      exact congrArg Fin.val h
    rw [ht] at h
    exact h
  have hmap2 :
      (order' ⟨2, by omega⟩ : α) =
        (order (cyclicIndex n hn i 2) : α) := by
    have h := hmap 2
    have ht :
        cyclicIndex n hn target 2 = ⟨2, by omega⟩ := by
      have h :=
        cyclicIndex_eq_mk_add_of_lt n hn target 2 (by
          dsimp [target, n]
          omega)
      apply Fin.ext
      exact congrArg Fin.val h
    rw [ht] at h
    exact h
  have hmap3 :
      (order' ⟨3, by omega⟩ : α) =
        (order (cyclicIndex n hn i 3) : α) := by
    have h := hmap 3
    have ht :
        cyclicIndex n hn target 3 = ⟨3, by omega⟩ := by
      have h :=
        cyclicIndex_eq_mk_add_of_lt n hn target 3 (by
          dsimp [target, n]
          omega)
      apply Fin.ext
      exact congrArg Fin.val h
    rw [ht] at h
    exact h

  have hgoodStart :
      DangerousHyperplaneEdgeGood order' ⟨0, by omega⟩ := by
    unfold DangerousHyperplaneEdgeGood at hgood0 ⊢
    have hnext :
        cyclicIndex n hn (⟨0, by omega⟩ : Fin n) 1 =
          ⟨1, by omega⟩ := by
      have h := cyclicIndex_eq_mk_add_of_lt n hn
        (⟨0, by omega⟩ : Fin n) 1 (by dsimp [n]; omega)
      apply Fin.ext
      exact congrArg Fin.val h
    rw [hnext, hmap0, hmap1]
    simpa [n, hn] using hgood0

  have hgoodTwo :
      DangerousHyperplaneEdgeGood order' ⟨2, by omega⟩ := by
    unfold DangerousHyperplaneEdgeGood at hgood2 ⊢
    have hnext :
        cyclicIndex n hn (⟨2, by omega⟩ : Fin n) 1 =
          ⟨3, by omega⟩ := by
      have h := cyclicIndex_eq_mk_add_of_lt n hn
        (⟨2, by omega⟩ : Fin n) 1 (by dsimp [n]; omega)
      apply Fin.ext
      exact congrArg Fin.val h
    rw [hnext, hmap2, hmap3]
    have hadd :
        cyclicIndex n hn
            (cyclicIndex n hn i 2) 1 =
          cyclicIndex n hn i 3 := by
      rw [cyclicIndex_add]
    simpa [n, hn, hadd] using hgood2

  exact ⟨order', hOrder', hgoodStart, hgoodTwo⟩

end

end Rank4DangerousBranches
end HigherRankKUM
