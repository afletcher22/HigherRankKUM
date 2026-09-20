import HigherRankKUM.Rank4.DangerousScheduleSymbolic

namespace HigherRankKUM
namespace Rank4DangerousScheduleSymbolic

open Set
open scoped Matroid
open Rank4GcdTwoDeletion
open Rank4DangerousBranches

noncomputable section

variable {α : Type*}

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
    apply Fin.ext
    simp [cyclicIndex]

  refine ⟨adjacentOrder (by omega) hH eC order,
    adjacent_cbo_of_symbolic_windows (by omega) hH eC order ?_⟩
  intro p
  rw [adjacentWindow_four_next]
  rcases p with p | r
  · rcases p with ⟨j, r⟩
    have hjlt := j.isLt
    fin_cases r
    · let m : Fin (k + 1) := ⟨j.val, by omega⟩
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
    · by_cases hj : j.val + 1 < k
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
        convert h using 1
        ext z
        simp [m, q, hj, hjEq, Set.mem_insert_iff, Set.mem_singleton_iff]  <;> tauto
    · by_cases hj : j.val + 1 < k
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
        convert h using 1
        ext z
        simp [m, q, hj, hjEq, Set.mem_insert_iff, Set.mem_singleton_iff]  <;> tauto
    · by_cases hj : j.val + 1 < k
      · let m : Fin (k + 1) := ⟨j.val + 1, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val + 2, by omega⟩
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
        have hEdge :
            cyclicIndex (3 * k + 1) (by omega)
                (⟨3 * k - 1, by omega⟩ : Fin (3 * k + 1)) 1 =
              ⟨3 * k, by omega⟩ :=
          cyclicIndex_eq_mk_add_of_lt _ _ _ _ (by omega)
        dsimp only at hExcEnd
        rw [hEdge] at hExcEnd
        convert hExcEnd using 1
        ext z
        simp [hj, hjEq, iT, iW, heT, heW,
            Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]  <;> tauto
  · fin_cases r
    · have hEdge :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨3 * k - 1, by omega⟩ : Fin (3 * k + 1)) 1 =
            ⟨3 * k, by omega⟩ :=
        cyclicIndex_eq_mk_add_of_lt _ _ _ _ (by omega)
      have hWrap :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) 1 =
            ⟨0, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      dsimp only at hExcWrap
      rw [hEdge, hWrap] at hExcWrap
      convert hExcWrap using 1
      ext z
      simp [iT, iW, heT, heW,
          Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]  <;> tauto
    · let m : Fin (k + 1) := ⟨0, by omega⟩
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
      convert h using 1
      ext z
      simp [m, q, iW, heW, Set.mem_insert_iff, Set.mem_singleton_iff]  <;> tauto

end

end Rank4DangerousScheduleSymbolic
end HigherRankKUM
