import HigherRankKUM.Rank4.DangerousBranchT2Geometry
import HigherRankKUM.Rank4.CyclicPigeonhole
import Mathlib.Data.Set.Card

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- A complementary side class in the two-dangerous-hyperplane branch has
ambient rank two or three. -/
theorem dangerous_two_complement_rank_two_or_three
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K) :
    M.eRk (M.E \ H) = (2 : ℕ∞) ∨
      M.eRk (M.E \ H) = (3 : ℕ∞) := by
  let A : Set α := M.E \ H
  have hAK : A ⊆ K :=
    dangerous_complement_subset_other
      hE hRank hEcard hStrict hH hK hne
  have hRkLe : M.eRk A ≤ (3 : ℕ∞) := by
    calc
      M.eRk A ≤ M.eRk K := M.eRk_mono hAK
      _ = (3 : ℕ∞) := hK.2.1
  have hAfin : A.Finite := by
    dsimp [A]
    exact hE.sdiff
  have hAcard : A.ncard = k + 1 := by
    dsimp [A]
    exact dangerous_complement_ncard_eq hE hEcard hH
  have hAnonempty : A.Nonempty := by
    rw [← Set.ncard_pos hAfin, hAcard]
    omega
  have hAproper : A ≠ M.E := by
    intro hEq
    have hHempty : H = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hxH
      have hxE := hH.subset_ground hxH
      have hxA : x ∈ A := by simpa [hEq] using hxE
      exact hxA.2 hxH
    have hr := hH.2.1
    rw [hHempty, M.eRk_empty] at hr
    norm_num at hr
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRkLe
  have hjleNat : j ≤ 3 := by exact_mod_cast hjle
  have hs := hStrict A (by
    dsimp [A]
    exact Set.sdiff_subset) hAnonempty hAproper
  rw [← hAfin.cast_ncard_eq, hAcard, hj] at hs
  have hsNat : 4 * (k + 1) < (4 * k + 2) * j := by
    exact_mod_cast hs
  have hjCases : j = 2 ∨ j = 3 := by omega
  rcases hjCases with rfl | rfl
  · left
    simpa [A] using hj
  · right
    simpa [A] using hj

/-- In the rank-two side case, the side closure has at most 2k elements. -/
theorem dangerous_two_complement_closure_ncard_le
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K)
    (hArank : M.eRk (M.E \ H) = (2 : ℕ∞)) :
    (M.closure (M.E \ H)).ncard ≤ 2 * k := by
  let A : Set α := M.E \ H
  let F : Set α := M.closure A
  have hAfin : A.Finite := by
    dsimp [A]
    exact hE.sdiff
  have hAcard : A.ncard = k + 1 := by
    dsimp [A]
    exact dangerous_complement_ncard_eq hE hEcard hH
  have hAnonempty : A.Nonempty := by
    rw [← Set.ncard_pos hAfin, hAcard]
    omega
  have hAsubE : A ⊆ M.E := by
    dsimp [A]
    exact Set.sdiff_subset
  have hFsubE : F ⊆ M.E := by
    dsimp [F]
    exact M.closure_subset_ground A
  have hFfin : F.Finite := hE.subset hFsubE
  have hFnonempty : F.Nonempty :=
    hAnonempty.mono (M.subset_closure A)
  have hFrank : M.eRk F = (2 : ℕ∞) := by
    dsimp [F]
    rw [M.eRk_closure_eq, hArank]
  have hFproper : F ≠ M.E := by
    intro hEq
    have hr := hFrank
    rw [hEq, M.eRk_ground, hRank] at hr
    norm_num at hr
  have hs := hStrict F hFsubE hFnonempty hFproper
  rw [← hFfin.cast_ncard_eq, hFrank] at hs
  have hsNat : 4 * F.ncard < (4 * k + 2) * 2 := by
    exact_mod_cast hs
  dsimp [F] at hsNat ⊢
  omega

/-- In the rank-two side case, at most k-1 core elements lie in the closure
of that side. -/
theorem dangerous_two_core_inter_complement_closure_ncard_le
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K)
    (hArank : M.eRk (M.E \ H) = (2 : ℕ∞)) :
    ((H ∩ K) ∩ M.closure (M.E \ H)).ncard ≤ k - 1 := by
  let A : Set α := M.E \ H
  let G : Set α := H ∩ K
  let B : Set α := G ∩ M.closure A
  have hAfin : A.Finite := by
    dsimp [A]
    exact hE.sdiff
  have hAcard : A.ncard = k + 1 := by
    dsimp [A]
    exact dangerous_complement_ncard_eq hE hEcard hH
  have hBsubClosure : B ⊆ M.closure A := by
    dsimp [B]
    exact Set.inter_subset_right
  have hAsubClosure : A ⊆ M.closure A := M.subset_closure A
  have hABsub : A ∪ B ⊆ M.closure A :=
    Set.union_subset hAsubClosure hBsubClosure
  have hABdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact hxA.2 hxB.1.1
  have hBfin : B.Finite := by
    exact (hE.subset (by
      intro x hx
      exact hH.subset_ground hx.1.1)).inter_of_left _
  have hUnionCard : (A ∪ B).ncard = A.ncard + B.ncard :=
    Set.ncard_union_eq hAfin hBfin hABdisj
  have hClosureFin : (M.closure A).Finite :=
    hE.subset (M.closure_subset_ground A)
  have hSubCard : (A ∪ B).ncard ≤ (M.closure A).ncard :=
    Set.ncard_le_ncard hABsub hClosureFin
  have hClosureBound : (M.closure A).ncard ≤ 2 * k := by
    dsimp [A]
    exact dangerous_two_complement_closure_ncard_le
      hk hE hRank hEcard hStrict hH hK hne hArank
  rw [hUnionCard, hAcard] at hSubCard
  dsimp [B, G, A] at hSubCard ⊢
  omega

end

end Rank4DangerousBranches
end HigherRankKUM
