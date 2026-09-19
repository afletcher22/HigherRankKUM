import HigherRankKUM.Rank4.DangerousBranchT2Geometry
import Mathlib.Combinatorics.Matroid.Minor.Contract

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
