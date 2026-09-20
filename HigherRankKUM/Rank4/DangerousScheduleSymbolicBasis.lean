import HigherRankKUM.Rank4.DangerousScheduleSymbolic

namespace HigherRankKUM
namespace Rank4DangerousScheduleSymbolic

open Set
open scoped Matroid
open Rank4GcdTwoDeletion
open Rank4DangerousBranches

noncomputable section

variable {α : Type*}

-- Symbolic adjacent certification; all finite-index arithmetic is confined to helper lemmas below.
set_option maxHeartbeats 800000 in
/-- Adjacent-good normalized dangerous-hyperplane construction, proved
entirely through the symbolic schedule API. -/
theorem exists_cbo_of_adjacent_good_normalized_symbolic
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder : CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (hgoodEnd :
      DangerousHyperplaneEdgeGood order ⟨3 * k - 1, by omega⟩)
    (hgoodWrap :
      DangerousHyperplaneEdgeGood order ⟨3 * k, by omega⟩) :
    ∃ σ : Fin (4 * k + 2) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) σ := by
  let iEnd : Fin (3 * k + 1) := ⟨3 * k - 1, by omega⟩
  have hnextEnd :
      cyclicIndex (3 * k + 1) (by omega) iEnd 1 =
        ⟨3 * k, by omega⟩ := by
    have h := cyclicIndex_eq_mk_add_of_lt (3 * k + 1) (by omega)
      iEnd 1 (by dsimp [iEnd]; omega)
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [iEnd] at hv ⊢
    omega
  have hgoodEnd' : DangerousHyperplaneEdgeGood order iEnd := by
    simpa [iEnd] using hgoodEnd
  have hgoodNext :
      DangerousHyperplaneEdgeGood order
        (cyclicIndex (3 * k + 1) (by omega) iEnd 1) := by
    rw [hnextEnd]
    exact hgoodWrap
  obtain ⟨cT, cW, hcne, hcT, hcW, hExcEnd, hExcWrap⟩ :=
    dangerous_hyperplane_adjacent_good_selection
      hk hE hRank hEcard hStrict hH order hOrder
      iEnd hgoodEnd' hgoodNext

  let C : Set α := M.E \ H
  have hCfin : C.Finite := by
    dsimp [C]
    exact hE.sdiff
  have hCcard : C.ncard = k + 1 := by
    dsimp [C]
    exact dangerous_complement_ncard_eq hE hEcard hH
  let iT : Fin (k + 1) := ⟨k, by omega⟩
  let iW : Fin (k + 1) := ⟨0, by omega⟩
  have hiTW : iT ≠ iW := by
    intro h
    have hv := congrArg Fin.val h
    simp [iT, iW] at hv
    omega
  obtain ⟨eC, heT, heW⟩ :=
    FiniteSchedule.exists_fin_equiv_with_two_prescribed
      hCfin hCcard iT iW hiTW hcT hcW hcne
  have heT' : (eC (⟨k, by omega⟩ : Fin (k + 1)) : α) = cT := by
    simpa [iT] using heT
  have heW' : (eC (⟨0, by omega⟩ : Fin (k + 1)) : α) = cW := by
    simpa [iW] using heW

  have hOrd
      (m : Fin (k + 1)) (q : Fin (3 * k + 1)) :
      M.IsBase
        ({(eC m : α),
          (order q : α),
          (order (cyclicIndex (3 * k + 1) (by omega) q 1) : α),
          (order (cyclicIndex (3 * k + 1) (by omega) q 2) : α)} : Set α) :=
    dangerous_hyperplane_complement_plus_core_triple_isBase
      hRank hH order hOrder (eC m).property q

  have hcoreNoWrap
      (q : Fin (3 * k + 1)) (d : ℕ)
      (hqd : q.val + d < 3 * k + 1) :
      cyclicIndex (3 * k + 1) (by omega) q d =
        ⟨q.val + d, hqd⟩ :=
    cyclicIndex_eq_mk_add_of_lt _ _ _ _ hqd

  have hcoreWrap1 :
      cyclicIndex (3 * k + 1) (by omega)
          (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) 1 =
        ⟨0, by omega⟩ := by
    apply Fin.ext
    simp [cyclicIndex]

  have hcoreWrap2 :
      cyclicIndex (3 * k + 1) (by omega)
          (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) 2 =
        ⟨1, by omega⟩ := by
    have hge : 3 * k + 1 ≤ 3 * k + 2 := by omega
    have hlt : 3 * k + 2 < 2 * (3 * k + 1) := by omega
    have h := cyclicIndex_eq_mk_sub_of_ge_of_lt_two_mul
      (3 * k + 1) (by omega)
      (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) 2 hge hlt
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa using hv

  refine ⟨adjacentOrder (by omega) hH eC order,
    adjacent_cbo_of_symbolic_windows (by omega) hH eC order ?_⟩
  intro p
  rw [adjacentWindow_four_next]
  rcases p with p | r
  · rcases p with ⟨j, r⟩
    have hjlt := j.isLt
    have hrCases : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 := by
      omega
    rcases hrCases with hr | hr | hr | hr
    · have hrEq : r = (0 : Fin 4) := by
        apply Fin.ext
        exact hr
      subst r
      let m : Fin (k + 1) := ⟨j.val, by omega⟩
      let q : Fin (3 * k + 1) := ⟨3 * j.val, by omega⟩
      have h := hOrd m q
      have hq1 := hcoreNoWrap q 1 (by
        dsimp [q]
        omega)
      have hq2 := hcoreNoWrap q 2 (by
        dsimp [q]
        omega)
      rw [hq1, hq2] at h
      simpa [m, q] using h
    · have hrEq : r = (1 : Fin 4) := by
        apply Fin.ext
        exact hr
      subst r
      by_cases hj : j.val + 1 < k
      · let m : Fin (k + 1) := ⟨j.val + 1, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val, by omega⟩
        have h := hOrd m q
        have hq1 := hcoreNoWrap q 1 (by
          dsimp [q]
          omega)
        have hq2 := hcoreNoWrap q 2 (by
          dsimp [q]
          omega)
        rw [hq1, hq2] at h
        convert h using 1
        ext z
        simp [m, q, hj, Set.mem_insert_iff, Set.mem_singleton_iff]  <;> tauto
      · have hjEq : j.val = k - 1 := by omega
        let m : Fin (k + 1) := ⟨k, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val, by omega⟩
        have h := hOrd m q
        have hq1 := hcoreNoWrap q 1 (by
          dsimp [q]
          omega)
        have hq2 := hcoreNoWrap q 2 (by
          dsimp [q]
          omega)
        rw [hq1, hq2] at h
        have hnextTail :=
          adjacentNext_block3_of_not_lt (k := k) (by omega) j hj
        simp only [adjacentNext_block1, adjacentNext_block2]
        rw [hnextTail]
        simp only [adjacentSymbolicOrder_block_g0, adjacentSymbolicOrder_block_g1,
          adjacentSymbolicOrder_block_g2, adjacentSymbolicOrder_tail_c]
        convert h using 1
        ext z
        simp [m, q, hjEq, Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto
    · have hrEq : r = (2 : Fin 4) := by
        apply Fin.ext
        exact hr
      subst r
      by_cases hj : j.val + 1 < k
      · let m : Fin (k + 1) := ⟨j.val + 1, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val + 1, by omega⟩
        have h := hOrd m q
        have hq1 := hcoreNoWrap q 1 (by
          dsimp [q]
          omega)
        have hq2 := hcoreNoWrap q 2 (by
          dsimp [q]
          omega)
        rw [hq1, hq2] at h
        convert h using 1
        ext z
        simp [m, q, hj, Set.mem_insert_iff, Set.mem_singleton_iff]  <;> tauto
      · have hjEq : j.val = k - 1 := by omega
        let m : Fin (k + 1) := ⟨k, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val + 1, by omega⟩
        have h := hOrd m q
        have hq1 := hcoreNoWrap q 1 (by
          dsimp [q]
          omega)
        have hq2 := hcoreNoWrap q 2 (by
          dsimp [q]
          omega)
        rw [hq1, hq2] at h
        have hlastCore :
            (⟨q.val + 2, by
                dsimp [q]
                omega⟩ : Fin (3 * k + 1)) =
              ⟨3 * k, by omega⟩ := by
          apply Fin.ext
          dsimp [q]
          omega
        rw [hlastCore] at h
        have hnextTail :=
          adjacentNext_block3_of_not_lt (k := k) (by omega) j hj
        simp only [adjacentNext_block2]
        rw [hnextTail]
        simp only [adjacentNext_tail0, adjacentSymbolicOrder_block_g1,
          adjacentSymbolicOrder_block_g2, adjacentSymbolicOrder_tail_c,
          adjacentSymbolicOrder_tail_g]
        dsimp [m, q] at h
        convert h using 1
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hz
          rcases hz with hz | hz | hz | hz
          · exact Or.inr (Or.inl hz)
          · exact Or.inr (Or.inr (Or.inl hz))
          · exact Or.inl hz
          · exact Or.inr (Or.inr (Or.inr hz))
        · intro hz
          rcases hz with hz | hz | hz | hz
          · exact Or.inr (Or.inr (Or.inl hz))
          · exact Or.inl hz
          · exact Or.inr (Or.inl hz)
          · exact Or.inr (Or.inr (Or.inr hz))
    · have hrEq : r = (3 : Fin 4) := by
        apply Fin.ext
        exact hr
      subst r
      by_cases hj : j.val + 1 < k
      · let m : Fin (k + 1) := ⟨j.val + 1, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val + 2, by omega⟩
        have h := hOrd m q
        have hq1 := hcoreNoWrap q 1 (by
          dsimp [q]
          omega)
        have hq2 := hcoreNoWrap q 2 (by
          dsimp [q]
          omega)
        have hq1' :
            cyclicIndex (3 * k + 1) (by omega) q 1 =
              ⟨3 * (j.val + 1), by omega⟩ := by
          rw [hq1]
          apply Fin.ext
          dsimp [q]
          omega
        have hq2' :
            cyclicIndex (3 * k + 1) (by omega) q 2 =
              ⟨3 * (j.val + 1) + 1, by omega⟩ := by
          rw [hq2]
          apply Fin.ext
          dsimp [q]
          omega
        rw [hq1', hq2'] at h
        have hnext :=
          adjacentNext_block3_of_lt (k := k) (by omega) j hj
        rw [hnext]
        simp only [adjacentNext_block0, adjacentNext_block1,
          adjacentSymbolicOrder_block_g2, adjacentSymbolicOrder_block_c,
          adjacentSymbolicOrder_block_g0, adjacentSymbolicOrder_block_g1]
        dsimp [m, q] at h
        convert h using 1
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        aesop
      · have hjEq : j.val = k - 1 := by omega
        have hnextTail :=
          adjacentNext_block3_of_not_lt (k := k) (by omega) j hj
        simp only [hnextTail, adjacentNext_tail0, adjacentNext_tail1,
          adjacentSymbolicOrder_block_g2, adjacentSymbolicOrder_tail_c,
          adjacentSymbolicOrder_tail_g, adjacentSymbolicOrder_block_c]
        have hEdge :
            cyclicIndex (3 * k + 1) (by omega)
                (⟨3 * k - 1, by omega⟩ : Fin (3 * k + 1)) 1 =
              ⟨3 * k, by omega⟩ := by
          simpa [iEnd] using hnextEnd
        rw [hEdge] at hExcEnd
        have hlast :
            (⟨3 * j.val + 2, by omega⟩ : Fin (3 * k + 1)) =
              iEnd := by
          apply Fin.ext
          dsimp [iEnd]
          omega
        rw [hlast, heT', heW']
        convert hExcEnd using 1
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
        tauto
  · have hrCases : r.val = 0 ∨ r.val = 1 := by
      omega
    rcases hrCases with hr | hr
    · have hrEq : r = (0 : Fin 2) := by
        apply Fin.ext
        exact hr
      subst r
      simp only [adjacentNext_tail0, adjacentNext_tail1, adjacentNext_block0,
          adjacentSymbolicOrder_tail_c, adjacentSymbolicOrder_tail_g,
          adjacentSymbolicOrder_block_c, adjacentSymbolicOrder_block_g0]
      have hEdge :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨3 * k - 1, by omega⟩ : Fin (3 * k + 1)) 1 =
            ⟨3 * k, by omega⟩ := by
        simpa [iEnd] using hnextEnd
      have hWrap :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) 1 =
            ⟨0, by omega⟩ := hcoreWrap1
      rw [hEdge, hWrap] at hExcWrap
      rw [heT', heW']
      convert hExcWrap using 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    · have hrEq : r = (1 : Fin 2) := by
        apply Fin.ext
        exact hr
      subst r
      simp only [adjacentNext_tail1, adjacentNext_block0, adjacentNext_block1,
          adjacentSymbolicOrder_tail_g, adjacentSymbolicOrder_block_c,
          adjacentSymbolicOrder_block_g0, adjacentSymbolicOrder_block_g1]
      let m : Fin (k + 1) := ⟨0, by omega⟩
      let q : Fin (3 * k + 1) := ⟨3 * k, by omega⟩
      have h := hOrd m q
      have hq1 :
          cyclicIndex (3 * k + 1) (by omega) q 1 =
            ⟨0, by omega⟩ := by
        simpa [q] using hcoreWrap1
      have hq2 :
          cyclicIndex (3 * k + 1) (by omega) q 2 =
            ⟨1, by omega⟩ := by
        simpa [q] using hcoreWrap2
      rw [hq1, hq2] at h
      dsimp [m, q] at h
      have h' :
          M.IsBase
            ({cW,
              (order (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) : α),
              (order (⟨0, by omega⟩ : Fin (3 * k + 1)) : α),
              (order (⟨1, by omega⟩ : Fin (3 * k + 1)) : α)} : Set α) := by
        simpa only [heW'] using h
      convert h' using 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

end

end Rank4DangerousScheduleSymbolic
end HigherRankKUM
