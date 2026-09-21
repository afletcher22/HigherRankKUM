import HigherRankKUM.Rank4.DangerousHyperplaneGood
import HigherRankKUM.Rank4.SaturatedFlatRankThree
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4SaturatedFlatGood

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- The complement of a saturated rank-three flat of size 3k has k+2
elements in a rank-four 4k+2 instance. -/
theorem saturated_complement_ncard_eq_k_add_two
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hE : M.E.Finite)
    (hEcard : M.E.ncard = 4 * k + 2)
    (hHsub : H ⊆ M.E)
    (hHcard : H.ncard = 3 * k) :
    (M.E \ H).ncard = k + 2 := by
  have hdiff : (M.E \ H).ncard = M.E.ncard - H.ncard :=
    Set.ncard_sdiff' hHsub hE
  rw [hdiff, hEcard, hHcard]
  omega

/-- In a strict rank-four 4k+2 instance, the complement of a saturated
rank-three flat has rank 2, 3, or 4. Rank 0 and 1 are excluded by strict
density and the complement cardinality k+2. -/
theorem saturated_complement_rank_trichotomy
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.ncard = 4 * k + 2)
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hHsub : H ⊆ M.E)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (hHcard : H.ncard = 3 * k) :
    M.eRk (M.E \ H) = (2 : ℕ∞) ∨
      M.eRk (M.E \ H) = (3 : ℕ∞) ∨
      M.eRk (M.E \ H) = (4 : ℕ∞) := by
  let C : Set α := M.E \ H
  have hCfin : C.Finite := by
    dsimp [C]
    exact hE.sdiff
  have hCcard : C.ncard = k + 2 := by
    dsimp [C]
    exact saturated_complement_ncard_eq_k_add_two
      hE hEcard hHsub hHcard
  have hCnonempty : C.Nonempty := by
    rw [← Set.ncard_pos hCfin, hCcard]
    omega
  have hCsub : C ⊆ M.E := by
    dsimp [C]
    exact Set.sdiff_subset
  have hCproper : C ≠ M.E := by
    intro hEq
    have hHempty : H = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hxH
      have hxE := hHsub hxH
      have hxC : x ∈ C := by simpa [hEq] using hxE
      exact hxC.2 hxH
    have hr := hHrank
    rw [hHempty, M.eRk_empty] at hr
    norm_num at hr
  have hRkLe : M.eRk C ≤ (4 : ℕ∞) := by
    rw [← hRank]
    exact M.eRk_le_eRank C
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRkLe
  have hjleNat : j ≤ 4 := by
    exact_mod_cast hjle
  have hs := hStrict C hCsub hCnonempty hCproper
  rw [← hCfin.cast_ncard_eq, hCcard, hj] at hs
  have hsNat : 4 * (k + 2) < (4 * k + 2) * j := by
    exact_mod_cast hs
  have hjge : 2 ≤ j := by
    by_contra h
    have : j ≤ 1 := by omega
    interval_cases j <;> omega
  have hjCases : j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hjCases with rfl | rfl | rfl
  · left
    simpa [C] using hj
  · right; left
    simpa [C] using hj
  · right; right
    simpa [C] using hj

/-- A core edge of a rank-three CBO is good when adjoining it to the
complement of the saturated flat has ambient rank four. -/
def SaturatedFlatEdgeGood
    {M : Matroid α} {k : ℕ} {H : Set α}
    (order : Fin (3 * k) ≃ (M.restrict H).E)
    (i : Fin (3 * k)) : Prop :=
  M.eRk
      ((M.E \ H) ∪
        ({(order i : α),
          (order (cyclicIndex (3 * k) (by omega) i 1) : α)} : Set α)) =
    (4 : ℕ∞)

/-- Every three consecutive entries of a rank-three CBO of H form an
ambient basis of H. -/
theorem saturated_core_triple_isBasis
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 0 < k)
    (hHsub : H ⊆ M.E)
    (order : Fin (3 * k) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (i : Fin (3 * k)) :
    M.IsBasis
      ({(order i : α),
        (order (cyclicIndex (3 * k) (by omega) i 1) : α),
        (order (cyclicIndex (3 * k) (by omega) i 2) : α)} : Set α)
      H := by
  have hB := hOrder i
  rw [cyclicWindow_three_eq] at hB
  exact (M.isBase_restrict_iff hHsub).1 hB

/-- A core basis triple together with the full complement has ambient rank
four. -/
theorem saturated_complement_union_core_triple_rank_four
    {M : Matroid α} {k : ℕ} {H I : Set α}
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.ncard = 4 * k + 2)
    (hHsub : H ⊆ M.E)
    (hHflat : M.IsFlat H)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (hHcard : H.ncard = 3 * k)
    (hI : M.IsBasis I H) :
    M.eRk ((M.E \ H) ∪ I) = (4 : ℕ∞) := by
  let C : Set α := M.E \ H
  have hCfin : C.Finite := by
    dsimp [C]
    exact hE.sdiff
  have hCcard : C.ncard = k + 2 := by
    dsimp [C]
    exact saturated_complement_ncard_eq_k_add_two
      hE hEcard hHsub hHcard
  have hCnonempty : C.Nonempty := by
    rw [← Set.ncard_pos hCfin, hCcard]
    omega
  obtain ⟨c, hc⟩ := hCnonempty
  have hbase :=
    Rank4DangerousBranches.isBase_of_rankThree_basis_and_outside
      hRank hI hHflat hHrank hc.1 hc.2
  have hsub : insert c I ⊆ C ∪ I := by
    intro x hx
    rcases hx with rfl | hxI
    · exact Or.inl hc
    · exact Or.inr hxI
  have hlower := M.eRk_mono hsub
  have hbaseRank : M.eRk (insert c I) = (4 : ℕ∞) := by
    rw [hbase.eRk_eq_eRank, hRank]
  rw [hbaseRank] at hlower
  apply le_antisymm
  · rw [← hRank]
    exact M.eRk_le_eRank _
  · simpa [C] using hlower

/-- Every three consecutive core edges contain a good edge. -/
theorem saturated_no_three_consecutive_bad_edges
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.ncard = 4 * k + 2)
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hHsub : H ⊆ M.E)
    (hHflat : M.IsFlat H)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (hHcard : H.ncard = 3 * k)
    (order : Fin (3 * k) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order) :
    ∀ i : Fin (3 * k),
      SaturatedFlatEdgeGood order i ∨
      SaturatedFlatEdgeGood order
        (cyclicIndex (3 * k) (by omega) i 1) ∨
      SaturatedFlatEdgeGood order
        (cyclicIndex (3 * k) (by omega) i 2) := by
  intro i
  let n := 3 * k
  let hn : 0 < n := by
    dsimp [n]
    omega
  let i1 : Fin n := cyclicIndex n hn i 1
  let i2 : Fin n := cyclicIndex n hn i 2
  let i3 : Fin n := cyclicIndex n hn i 3
  let a : α := (order i : α)
  let b : α := (order i1 : α)
  let c : α := (order i2 : α)
  let d : α := (order i3 : α)
  let C : Set α := M.E \ H

  have hCrank :
      M.eRk C = (2 : ℕ∞) ∨
      M.eRk C = (3 : ℕ∞) ∨
      M.eRk C = (4 : ℕ∞) := by
    simpa [C] using
      saturated_complement_rank_trichotomy
        hE hRank hEcard hStrict hHsub hHrank hHcard

  have hBasis0 :=
    saturated_core_triple_isBasis hk hHsub order hOrder i
  have hABC :
      M.eRk (C ∪ ({a, b, c} : Set α)) = (4 : ℕ∞) := by
    have h :=
      saturated_complement_union_core_triple_rank_four
        hk hE hRank hEcard hHsub hHflat hHrank hHcard hBasis0
    simpa [C, a, b, c, i1, i2, n, hn] using h

  have hBasis1 :=
    saturated_core_triple_isBasis hk hHsub order hOrder i1
  have hBCD :
      M.eRk (C ∪ ({b, c, d} : Set α)) = (4 : ℕ∞) := by
    have h :=
      saturated_complement_union_core_triple_rank_four
        hk hE hRank hEcard hHsub hHflat hHrank hHcard hBasis1
    have hadd1 :
        cyclicIndex n hn i1 1 = i2 := by
      dsimp [i1, i2]
      rw [cyclicIndex_add]
    have hadd2 :
        cyclicIndex n hn i1 2 = i3 := by
      dsimp [i1, i3]
      rw [cyclicIndex_add]
    simpa [C, b, c, d, i1, i2, i3, n, hn, hadd1, hadd2] using h

  have hgood :=
    Rank4DangerousBranches.one_of_three_pair_extensions_has_rank_four
      hRank hCrank hABC hBCD
  simpa [SaturatedFlatEdgeGood, C, a, b, c, d, i1, i2, i3, n, hn,
    cyclicIndex_add] using hgood

/-- A good saturated-core edge yields a loopless rank-two matroid on the
complement after contracting that core pair. -/
theorem saturated_good_pair_contract_complement_rank_two_loopless
    {M : Matroid α} {k : ℕ} {H P : Set α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hHflat : M.IsFlat H)
    (hP : M.Indep P)
    (hPsub : P ⊆ H)
    (hPrank : M.eRk P = (2 : ℕ∞))
    (hGood : M.eRk ((M.E \ H) ∪ P) = (4 : ℕ∞)) :
    let C : Set α := M.E \ H
    let N : Matroid α := (M.contract P).restrict C
    N.eRank = (2 : ℕ∞) ∧ N.Loopless := by
  let C : Set α := M.E \ H
  let Q : Matroid α := M.contract P
  let N : Matroid α := Q.restrict C
  have hPE : P ⊆ M.E := hP.subset_ground
  have hCQ : C ⊆ Q.E := by
    intro e heC
    change e ∈ M.E \ P
    refine ⟨heC.1, ?_⟩
    intro heP
    exact heC.2 (hPsub heP)
  have hrankEq :=
    eRk_union_eq_contract_eRk_add M hPE hCQ
  have hQrank : Q.eRk C = (2 : ℕ∞) := by
    have hadd : Q.eRk C + (2 : ℕ∞) = (2 : ℕ∞) + 2 := by
      calc
        Q.eRk C + (2 : ℕ∞) = M.eRk (C ∪ P) := by
          simpa [Q, hPrank] using hrankEq.symm
        _ = (4 : ℕ∞) := hGood
        _ = (2 : ℕ∞) + 2 := by norm_num
    exact ENat.add_left_injective_of_ne_top (by simp) hadd
  have hNrank : N.eRank = (2 : ℕ∞) := by
    dsimp [N]
    simpa [Q] using hQrank
  have hLoopless : N.Loopless := by
    rw [Matroid.loopless_iff_forall_isNonloop]
    intro e heN
    have heC : e ∈ C := by
      simpa [N, Q] using heN
    have hclPH : M.closure P ⊆ H := by
      intro x hx
      exact (M.mem_closure_iff_forall_mem_isFlat P hPE).1 hx
        H hHflat hPsub
    rw [Matroid.restrict_isNonloop_iff]
    refine ⟨?_, heC⟩
    rw [Matroid.contract_isNonloop_iff]
    exact ⟨heC.1, fun hecl => heC.2 (hclPH hecl)⟩
  exact ⟨hNrank, hLoopless⟩

end

end Rank4SaturatedFlatGood
end HigherRankKUM
