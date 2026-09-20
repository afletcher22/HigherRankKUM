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

  have hOrd
      (m : Fin (k + 1)) (q : Fin (3 * k + 1)) :
      M.IsBase
        ({(eC m : α),
          (order q : α),
          (order (cyclicIndex (3 * k + 1) (by omega) q 1) : α),
          (order (cyclicIndex (3 * k + 1) (by omega) q 2) : α)} : Set α) :=
    dangerous_hyperplane_complement_plus_core_triple_isBase
      hRank hH order hOrder (eC m).property q

  refine ⟨separatedOrder hk hH eC order,
    separated_cbo_of_symbolic_windows hk hH eC order ?_⟩
  intro p
  rw [transportedWindow_four_next]
  rcases p with r | p
  · fin_cases r
    · dsimp only at hExc0
      have h01 :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨0, by omega⟩ : Fin (3 * k + 1)) 1 =
            ⟨1, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      rw [h01] at hExc0
      convert hExc0 using 1 <;>
        simp [i0, i1, he0, he1,
          Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] <;>
        tauto
    · let m : Fin (k + 1) := ⟨1, by omega⟩
      let q : Fin (3 * k + 1) := ⟨0, by omega⟩
      have h := hOrd m q
      have hq1 :
          cyclicIndex (3 * k + 1) (by omega) q 1 =
            ⟨1, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex, q]
      have hq2 :
          cyclicIndex (3 * k + 1) (by omega) q 2 =
            ⟨2, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex, q]
      rw [hq1, hq2] at h
      convert h using 1 <;>
        simp [m, q, i1, he1,
          Set.mem_insert_iff, Set.mem_singleton_iff] <;>
        tauto
    · let m : Fin (k + 1) := ⟨1, by omega⟩
      let q : Fin (3 * k + 1) := ⟨1, by omega⟩
      have h := hOrd m q
      have hq1 :
          cyclicIndex (3 * k + 1) (by omega) q 1 =
            ⟨2, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex, q]
      have hq2 :
          cyclicIndex (3 * k + 1) (by omega) q 2 =
            ⟨3, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex, q]
      rw [hq1, hq2] at h
      convert h using 1 <;>
        simp [m, q, i1, he1,
          Set.mem_insert_iff, Set.mem_singleton_iff] <;>
        tauto
    · dsimp only at hExc2
      have h23 :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨2, by omega⟩ : Fin (3 * k + 1)) 1 =
            ⟨3, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      rw [h23] at hExc2
      convert hExc2 using 1 <;>
        simp [i1, i2, he1, he2,
          Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] <;>
        tauto
    · let m : Fin (k + 1) := ⟨2, by omega⟩
      let q : Fin (3 * k + 1) := ⟨2, by omega⟩
      have h := hOrd m q
      have hq1 :
          cyclicIndex (3 * k + 1) (by omega) q 1 =
            ⟨3, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex, q]
      have hq2 :
          cyclicIndex (3 * k + 1) (by omega) q 2 =
            ⟨4, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex, q]
        omega
      rw [hq1, hq2] at h
      convert h using 1 <;>
        simp [m, q, i2, he2,
          Set.mem_insert_iff, Set.mem_singleton_iff] <;>
        tauto
    · let m : Fin (k + 1) := ⟨2, by omega⟩
      let q : Fin (3 * k + 1) := ⟨3, by omega⟩
      have h := hOrd m q
      have hq1 :
          cyclicIndex (3 * k + 1) (by omega) q 1 =
            ⟨4, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex, q]
        omega
      have hq2 :
          cyclicIndex (3 * k + 1) (by omega) q 2 =
            ⟨5, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex, q]
        omega
      rw [hq1, hq2] at h
      convert h using 1 <;>
        simp [m, q, i2, he2,
          Set.mem_insert_iff, Set.mem_singleton_iff] <;>
        tauto
  · rcases p with ⟨j, r⟩
    fin_cases r
    · let m : Fin (k + 1) := ⟨j.val + 2, by omega⟩
      let q : Fin (3 * k + 1) := ⟨3 * j.val + 4, by omega⟩
      have h := hOrd m q
      have hq1 :
          cyclicIndex (3 * k + 1) (by omega) q 1 =
            ⟨3 * j.val + 5, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
      have hq2 :
          cyclicIndex (3 * k + 1) (by omega) q 2 =
            ⟨3 * j.val + 6, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
      rw [hq1, hq2] at h
      simpa [m, q] using h
    · by_cases hj : j.val + 1 < k - 1
      · let m : Fin (k + 1) := ⟨j.val + 3, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val + 4, by omega⟩
        have h := hOrd m q
        have hq1 :
            cyclicIndex (3 * k + 1) (by omega) q 1 =
              ⟨3 * j.val + 5, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
        have hq2 :
            cyclicIndex (3 * k + 1) (by omega) q 2 =
              ⟨3 * j.val + 6, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
        rw [hq1, hq2] at h
        convert h using 1 <;>
          simp [m, q, hj, Set.mem_insert_iff, Set.mem_singleton_iff] <;>
          tauto
      · have hjEq : j.val = k - 2 := by omega
        let m : Fin (k + 1) := ⟨0, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * k - 2, by omega⟩
        have h := hOrd m q
        have hq1 :
            cyclicIndex (3 * k + 1) (by omega) q 1 =
              ⟨3 * k - 1, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
          omega
        have hq2 :
            cyclicIndex (3 * k + 1) (by omega) q 2 =
              ⟨3 * k, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hq1, hq2] at h
        convert h using 1 <;>
          simp [m, q, hj, hjEq, i0, he0,
            Set.mem_insert_iff, Set.mem_singleton_iff] <;>
          tauto
    · by_cases hj : j.val + 1 < k - 1
      · let m : Fin (k + 1) := ⟨j.val + 3, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val + 5, by omega⟩
        have h := hOrd m q
        have hq1 :
            cyclicIndex (3 * k + 1) (by omega) q 1 =
              ⟨3 * j.val + 6, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
        have hq2 :
            cyclicIndex (3 * k + 1) (by omega) q 2 =
              ⟨3 * j.val + 7, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
        rw [hq1, hq2] at h
        convert h using 1 <;>
          simp [m, q, hj, Set.mem_insert_iff, Set.mem_singleton_iff] <;>
          tauto
      · have hjEq : j.val = k - 2 := by omega
        let m : Fin (k + 1) := ⟨0, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * k - 1, by omega⟩
        have h := hOrd m q
        have hq1 :
            cyclicIndex (3 * k + 1) (by omega) q 1 =
              ⟨3 * k, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
          omega
        have hq2 :
            cyclicIndex (3 * k + 1) (by omega) q 2 =
              ⟨0, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q]
          omega
        rw [hq1, hq2] at h
        convert h using 1 <;>
          simp [m, q, hj, hjEq, i0, he0,
            Set.mem_insert_iff, Set.mem_singleton_iff] <;>
          tauto
    · by_cases hj : j.val + 1 < k - 1
      · let m : Fin (k + 1) := ⟨j.val + 3, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * j.val + 6, by omega⟩
        have h := hOrd m q
        have hq1 :
            cyclicIndex (3 * k + 1) (by omega) q 1 =
              ⟨3 * j.val + 7, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
        have hq2 :
            cyclicIndex (3 * k + 1) (by omega) q 2 =
              ⟨3 * j.val + 8, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q, Nat.mod_eq_of_lt (by omega)]
        rw [hq1, hq2] at h
        convert h using 1 <;>
          simp [m, q, hj, Set.mem_insert_iff, Set.mem_singleton_iff] <;>
          tauto
      · have hjEq : j.val = k - 2 := by omega
        let m : Fin (k + 1) := ⟨0, by omega⟩
        let q : Fin (3 * k + 1) := ⟨3 * k, by omega⟩
        have h := hOrd m q
        have hq1 :
            cyclicIndex (3 * k + 1) (by omega) q 1 =
              ⟨0, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q]
        have hq2 :
            cyclicIndex (3 * k + 1) (by omega) q 2 =
              ⟨1, by omega⟩ := by
          apply Fin.ext
          simp [cyclicIndex, q]
        rw [hq1, hq2] at h
        convert h using 1 <;>
          simp [m, q, hj, hjEq, i0, he0,
            Set.mem_insert_iff, Set.mem_singleton_iff] <;>
          tauto

end

end Rank4DangerousScheduleSymbolic
end HigherRankKUM
