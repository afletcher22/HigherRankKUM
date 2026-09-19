import HigherRankKUM.Rank4.DangerousBranchT2Geometry
import Mathlib.Combinatorics.Matroid.Minor.Contract
import HigherRankKUM.TightContraction

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- The complement of a dangerous hyperplane has ambient rank 2, 3, or 4.
Rank 0 and rank 1 are excluded by strict density and its cardinality `k+1`. -/
theorem dangerous_complement_rank_trichotomy
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H) :
    M.eRk (M.E \ H) = (2 : ℕ∞) ∨
      M.eRk (M.E \ H) = (3 : ℕ∞) ∨
      M.eRk (M.E \ H) = (4 : ℕ∞) := by
  let C : Set α := M.E \ H
  have hCfin : C.Finite := by
    dsimp [C]
    exact hE.sdiff
  have hCcard : C.ncard = k + 1 := by
    dsimp [C]
    exact dangerous_complement_ncard_eq hE hEcard hH
  have hCnonempty : C.Nonempty := by
    rw [← Set.ncard_pos hCfin, hCcard]
    omega
  have hCsub : C ⊆ M.E := by
    dsimp [C]
    exact Set.sdiff_subset
  have hRkLe : M.eRk C ≤ (4 : ℕ∞) := by
    rw [← hRank]
    exact M.eRk_le_eRank C
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRkLe
  have hjleNat : j ≤ 4 := by
    exact_mod_cast hjle
  have hCproper : C ≠ M.E := by
    intro hEq
    have hle := hRkLe
    rw [hEq, M.eRk_ground, hRank] at hle
    -- The complement being the whole ground would force H empty, contradicting
    -- its rank three; use that contradiction directly.
    have hHempty : H = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hxH
      have hxE := hH.subset_ground hxH
      have hxC : x ∈ C := by simpa [hEq] using hxE
      exact hxC.2 hxH
    have hr := hH.2.1
    rw [hHempty, M.eRk_empty] at hr
    norm_num at hr
  have hs := hStrict C hCsub hCnonempty hCproper
  rw [← hCfin.cast_ncard_eq, hCcard, hj] at hs
  have hsNat : 4 * (k + 1) < (4 * k + 2) * j := by
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


/-- A good independent core pair inside the unique dangerous hyperplane
produces a loopless rank-two matroid on the complement after contraction.

This is the common input for both t=1 selection subcases: common pairs for
adjacent good edges and the three-element path when good edges are separated. -/
theorem dangerous_one_good_pair_contract_complement_rank_two_loopless
    {M : Matroid α} {k : ℕ} {H P : Set α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hH : DangerousHyperplane M k H)
    (hP : M.Indep P)
    (hPsub : P ⊆ H)
    (hPrank : M.eRk P = (2 : ℕ∞))
    (hGood : M.eRk (P ∪ (M.E \ H)) = (4 : ℕ∞)) :
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
        _ = (4 : ℕ∞) := by simpa [C, Set.union_comm] using hGood
        _ = (2 : ℕ∞) + 2 := by norm_num
    exact ENat.add_right_injective_of_ne_top
      (n := (2 : ℕ∞)) (by simp) hadd
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
        H hH.1 hPsub
    rw [Matroid.restrict_isNonloop_iff]
    refine ⟨?_, heC⟩
    rw [Matroid.contract_isNonloop_iff]
    exact ⟨heC.1, fun hecl => heC.2 (hclPH hecl)⟩
  exact ⟨hNrank, hLoopless⟩

/-- Ordinary `t=1` window certificate: a basis of the unique dangerous
hyperplane plus any complementary element is an ambient basis. -/
theorem dangerous_one_hyperplane_basis_plus_complement_isBase
    {M : Matroid α} {k : ℕ} {H I : Set α} {c : α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hH : DangerousHyperplane M k H)
    (hI : M.IsBasis I H)
    (hc : c ∈ M.E \ H) :
    M.IsBase (insert c I) :=
  isBase_of_rankThree_basis_and_outside
    hRank hI hH.1 hH.2.1 hc.1 hc.2

/-- Contraction form of the exceptional `t=1` windows.  If `P` is an
independent core pair and `Q` is a basis after contracting `P`, then
`P ∪ Q` is an ambient basis. -/
theorem isBase_union_of_contract_isBase
    {M : Matroid α} {P Q : Set α}
    (hP : M.Indep P)
    (hQ : (M.contract P).IsBase Q) :
    M.IsBase (Q ∪ P) := by
  exact (hP.contract_isBase_iff.1 hQ).1

/-- Two complementary elements selected as a basis in the contraction by a
core edge give exactly the exceptional four-element basis needed by the
`t=1` patterns. -/
theorem dangerous_one_exceptional_window_isBase
    {M : Matroid α} {P : Set α} {c₀ c₁ : α}
    (hP : M.Indep P)
    (hQ : (M.contract P).IsBase ({c₀, c₁} : Set α)) :
    M.IsBase (({c₀, c₁} : Set α) ∪ P) :=
  isBase_union_of_contract_isBase hP hQ

end

end Rank4DangerousBranches
end HigherRankKUM
