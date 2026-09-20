import HigherRankKUM.Rank4.DangerousScheduleSymbolic

namespace HigherRankKUM
namespace Rank4DangerousScheduleSymbolic

open Set
open scoped Matroid
open Rank4GcdTwoDeletion
open Rank4DangerousBranches

noncomputable section

variable {α : Type*}

/-- Distance-two-good normalized dangerous-hyperplane construction,
proved through the symbolic separated schedule. -/
theorem exists_cbo_of_distance_two_good_normalized_symbolic
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder : CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (hgood0 : DangerousHyperplaneEdgeGood order ⟨0, by omega⟩)
    (hgood2 : DangerousHyperplaneEdgeGood order ⟨2, by omega⟩) :
    ∃ σ : Fin (4 * k + 2) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) σ := by
  have hidx2 :
      cyclicIndex (3 * k + 1) (by omega)
          (⟨0, by omega⟩ : Fin (3 * k + 1)) 2 =
        ⟨2, by omega⟩ := by
    apply Fin.ext
    simp [cyclicIndex]
    omega
  obtain ⟨c₀, c₁, c₂, hc01, hc12, hc02,
      hc₀, hc₁, hc₂, hExc0, hExc2⟩ :=
    dangerous_hyperplane_distance_two_good_selection
      hk hE hRank hEcard hStrict hH order hOrder
      ⟨0, by omega⟩ hgood0 (by rw [hidx2]; exact hgood2)

  let C : Set α := M.E \ H
  have hCfin : C.Finite := by
    dsimp [C]
    exact hE.sdiff
  have hCcard : C.ncard = k + 1 := by
    dsimp [C]
    exact dangerous_complement_ncard_eq hE hEcard hH

  let i0 : Fin (k + 1) := ⟨0, by omega⟩
  let i1 : Fin (k + 1) := ⟨1, by omega⟩
  let i2 : Fin (k + 1) := ⟨2, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0, i1] at hv
  have hi02 : i0 ≠ i2 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0, i2] at hv
  have hi12 : i1 ≠ i2 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i1, i2] at hv

  obtain ⟨eC, he0, he1, he2⟩ :=
    FiniteSchedule.exists_fin_equiv_with_three_at_positions
      hCfin hCcard i0 i1 i2 hi01 hi02 hi12
      hc₀ hc₁ hc₂ hc01 hc02 hc12
  have he0' : (eC (⟨0, by omega⟩ : Fin (k + 1)) : α) = c₀ := by
    rw [show (⟨0, by omega⟩ : Fin (k + 1)) = i0 by
      apply Fin.ext
      rfl]
    exact he0
  have he1' : (eC (⟨1, by omega⟩ : Fin (k + 1)) : α) = c₁ := by
    rw [show (⟨1, by omega⟩ : Fin (k + 1)) = i1 by
      apply Fin.ext
      rfl]
    exact he1
  have he2' : (eC (⟨2, by omega⟩ : Fin (k + 1)) : α) = c₂ := by
    rw [show (⟨2, by omega⟩ : Fin (k + 1)) = i2 by
      apply Fin.ext
      rfl]
    exact he2

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

  have hcoreLastMinusOne2 :
      cyclicIndex (3 * k + 1) (by omega)
          (⟨3 * k - 1, by omega⟩ : Fin (3 * k + 1)) 2 =
        ⟨0, by omega⟩ := by
    apply Fin.ext
    simp only [cyclicIndex_val, Fin.val_mk]
    have hsum : 3 * k - 1 + 2 = 3 * k + 1 := by omega
    rw [hsum, Nat.mod_self]

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
    rw [cyclicIndex_eq_mk_sub_of_ge_of_lt_two_mul
      (3 * k + 1) (by omega)
      (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) 2 hge hlt]
    apply Fin.ext
    simp

  refine ⟨separatedOrder hk hH eC order,
    separated_cbo_of_symbolic_windows hk hH eC order ?_⟩
  intro p
  rw [transportedWindow_four_next]
  simp only [transportedNext_separated]
  rcases p with r | p
  · fin_cases r
    · simp only [separatedNext_head0, separatedNext_head1, separatedNext_head2,
          separatedSymbolicOrder_head_c0, separatedSymbolicOrder_head_g0,
          separatedSymbolicOrder_head_g1, separatedSymbolicOrder_head_c1]
      have hlt01 : 0 + 1 < 3 * k + 1 := by omega
      have h01 :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨0, by omega⟩ : Fin (3 * k + 1)) 1 =
            ⟨1, by omega⟩ := by
        exact cyclicIndex_eq_mk_add_of_lt _ _ _ _ hlt01
      rw [h01] at hExc0
      rw [he0', he1']
      convert hExc0 using 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    · simp only [separatedNext_head1, separatedNext_head2, separatedNext_head3,
          separatedSymbolicOrder_head_g0, separatedSymbolicOrder_head_g1,
          separatedSymbolicOrder_head_c1, separatedSymbolicOrder_head_g2]
      let m : Fin (k + 1) := ⟨1, by omega⟩
      let q : Fin (3 * k + 1) := ⟨0, by omega⟩
      have h := hOrd m q
      have hq1 := hcoreNoWrap q 1 (by
        dsimp [q]
        omega)
      have hq2 := hcoreNoWrap q 2 (by
        dsimp [q]
        omega)
      rw [hq1, hq2] at h
      rw [he1']
      convert h using 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · simp only [separatedNext_head2, separatedNext_head3, separatedNext_head4,
          separatedSymbolicOrder_head_g1, separatedSymbolicOrder_head_c1,
          separatedSymbolicOrder_head_g2, separatedSymbolicOrder_head_g3]
      let m : Fin (k + 1) := ⟨1, by omega⟩
      let q : Fin (3 * k + 1) := ⟨1, by omega⟩
      have h := hOrd m q
      have hq1 := hcoreNoWrap q 1 (by
        dsimp [q]
        omega)
      have hq2 := hcoreNoWrap q 2 (by
        dsimp [q]
        omega)
      rw [hq1, hq2] at h
      rw [he1']
      convert h using 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · simp only [separatedNext_head3, separatedNext_head4, separatedNext_head5,
          separatedSymbolicOrder_head_c1, separatedSymbolicOrder_head_g2,
          separatedSymbolicOrder_head_g3, separatedSymbolicOrder_block_c]
      rw [hidx2] at hExc2
      have hlt23 : 2 + 1 < 3 * k + 1 := by omega
      have h23 :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨2, by omega⟩ : Fin (3 * k + 1)) 1 =
            ⟨3, by omega⟩ := by
        exact cyclicIndex_eq_mk_add_of_lt _ _ _ _ hlt23
      rw [h23] at hExc2
      rw [he1', he2']
      convert hExc2 using 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    · simp only [separatedNext_head4, separatedNext_head5, separatedNext_block0,
          separatedSymbolicOrder_head_g2, separatedSymbolicOrder_head_g3,
          separatedSymbolicOrder_block_c, separatedSymbolicOrder_block_g0]
      let m : Fin (k + 1) := ⟨2, by omega⟩
      let q : Fin (3 * k + 1) := ⟨2, by omega⟩
      have h := hOrd m q
      have hq1 := hcoreNoWrap q 1 (by
        dsimp [q]
        omega)
      have hq2 := hcoreNoWrap q 2 (by
        dsimp [q]
        omega)
      rw [hq1, hq2] at h
      rw [he2']
      convert h using 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · simp only [separatedNext_head5, separatedNext_block0, separatedNext_block1,
          separatedSymbolicOrder_head_g3, separatedSymbolicOrder_block_c,
          separatedSymbolicOrder_block_g0, separatedSymbolicOrder_block_g1]
      let m : Fin (k + 1) := ⟨2, by omega⟩
      let q : Fin (3 * k + 1) := ⟨3, by omega⟩
      have h := hOrd m q
      have hq1 := hcoreNoWrap q 1 (by
        dsimp [q]
        omega)
      have hq2 := hcoreNoWrap q 2 (by
        dsimp [q]
        omega)
      rw [hq1, hq2] at h
      rw [he2']
      convert h using 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
  · rcases p with ⟨j, r⟩
    have hjlt := j.isLt
    fin_cases r
    · let m : Fin (k + 1) := ⟨j.val + 2, by omega⟩
      let q : Fin (3 * k + 1) := ⟨3 * j.val + 4, by omega⟩
      have h := hOrd m q
      have hq1 := hcoreNoWrap q 1 (by
        dsimp [q]
        omega)
      have hq2 := hcoreNoWrap q 2 (by
        dsimp [q]
        omega)
      rw [hq1, hq2] at h
      simpa [m, q] using h
    · by_cases hj : j.val + 1 < k - 1
      · let m : Fin (k + 1) := ⟨j.val + 3, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val + 4, by omega⟩
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
      · have hjEq : j.val = k - 2 := by omega
        let m : Fin (k + 1) := ⟨0, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * k - 2, by omega⟩
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
        simp [m, q, hj, hjEq, i0, he0,
            Set.mem_insert_iff, Set.mem_singleton_iff]  <;> tauto
    · by_cases hj : j.val + 1 < k - 1
      · let m : Fin (k + 1) := ⟨j.val + 3, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val + 5, by omega⟩
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
      · have hjEq : j.val = k - 2 := by omega
        let m : Fin (k + 1) := ⟨0, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * k - 1, by omega⟩
        have h := hOrd m q
        have hq1 := hcoreNoWrap q 1 (by
          dsimp [q]
          omega)
        have hq2 :
            cyclicIndex (3 * k + 1) (by omega) q 2 =
              ⟨0, by omega⟩ := by
          simpa [q] using hcoreLastMinusOne2
        rw [hq1, hq2] at h
        convert h using 1
        ext z
        simp [m, q, hj, hjEq, i0, he0,
            Set.mem_insert_iff, Set.mem_singleton_iff]  <;> tauto
    · by_cases hj : j.val + 1 < k - 1
      · let m : Fin (k + 1) := ⟨j.val + 3, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val + 6, by omega⟩
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
      · have hjEq : j.val = k - 2 := by omega
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
        convert h using 1
        ext z
        simp [m, q, hj, hjEq, i0, he0,
            Set.mem_insert_iff, Set.mem_singleton_iff]  <;> tauto

end

end Rank4DangerousScheduleSymbolic
end HigherRankKUM
