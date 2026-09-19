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
  have hjge : 2 ≤ j := by
    by_contra h
    have hjle1 : j ≤ 1 := by omega
    interval_cases j <;> omega
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
  have hbound : F.ncard ≤ 2 * k := by
    by_contra h
    have hge : 2 * k + 1 ≤ F.ncard := by omega
    have hmul : 4 * (2 * k + 1) ≤ 4 * F.ncard :=
      Nat.mul_le_mul_left 4 hge
    omega
  simpa [F] using hbound

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
  have hBsubE : B ⊆ M.E := by
    intro x hx
    exact hH.subset_ground hx.1.1
  have hBfin : B.Finite := hE.subset hBsubE
  have hUnionCard : (A ∪ B).ncard = A.ncard + B.ncard :=
    Set.ncard_union_eq hABdisj hAfin hBfin
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


/-- In a rank-two side, any core element outside the side closure has a
two-element side witness that joins it to a basis of the containing dangerous
hyperplane. -/
theorem dangerous_two_rankTwo_side_good_of_not_mem_closure
    {M : Matroid α} {k : ℕ} {H K : Set α} {g : α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K)
    (hg : g ∈ H ∩ K)
    (hArank : M.eRk (M.E \ H) = (2 : ℕ∞))
    (hgcl : g ∉ M.closure (M.E \ H)) :
    ∃ x y : α, x ∈ M.E \ H ∧ y ∈ M.E \ H ∧ x ≠ y ∧
      M.IsBasis ({g, x, y} : Set α) K := by
  let A : Set α := M.E \ H
  obtain ⟨J, hJ⟩ := M.exists_isBasis A
  have hJcard : J.encard = (2 : ℕ∞) := by
    rw [hJ.encard_eq_eRk, hArank]
  obtain ⟨x, y, hxy, hJpair⟩ := Set.encard_eq_two.mp hJcard
  have hxA : x ∈ A := hJ.subset (by rw [hJpair]; simp)
  have hyA : y ∈ A := hJ.subset (by rw [hJpair]; simp)
  have hJK : J ⊆ K := by
    exact hJ.subset.trans
      (dangerous_complement_subset_other
        hE hRank hEcard hStrict hH hK hne)
  have hgE : g ∈ M.E := hH.subset_ground hg.1
  have hgJ : g ∉ J := by
    intro hgJ
    exact (hJ.subset hgJ).2 hg.1
  have hclJ : M.closure J = M.closure A := hJ.closure_eq_closure
  have hgclJ : g ∉ M.closure J := by
    rwa [hclJ]
  have hInd : M.Indep (insert g J) :=
    (hJ.indep.insert_indep_iff_of_notMem hgJ).2 ⟨hgE, hgclJ⟩
  have hSubK : insert g J ⊆ K := by
    intro z hz
    rcases hz with rfl | hz
    · exact hg.2
    · exact hJK hz
  have hRankInsert : M.eRk (insert g J) = (3 : ℕ∞) := by
    rw [M.eRk_insert_eq_add_one ⟨hgE, hgclJ⟩]
    rw [hJ.eRk_eq_eRk, hArank]
    norm_num
  have hBasisK : M.IsBasis (insert g J) K :=
    hInd.isBasis_of_eRk_ge (hE.subset hInd.subset_ground)
      hSubK (by rw [hK.2.1, hRankInsert])
  refine ⟨x, y, ?_, ?_, hxy, ?_⟩
  · simpa [A] using hxA
  · simpa [A] using hyA
  · simpa [hJpair] using hBasisK

/-- If the side itself has rank three, every core element is good. -/
theorem dangerous_two_rankThree_side_good
    {M : Matroid α} {k : ℕ} {H K : Set α} {g : α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K)
    (hg : g ∈ H ∩ K)
    (hArank : M.eRk (M.E \ H) = (3 : ℕ∞)) :
    ∃ x y : α, x ∈ M.E \ H ∧ y ∈ M.E \ H ∧ x ≠ y ∧
      M.IsBasis ({g, x, y} : Set α) K := by
  let A : Set α := M.E \ H
  have hAK : A ⊆ K :=
    dangerous_complement_subset_other
      hE hRank hEcard hStrict hH hK hne
  obtain ⟨J, hJA⟩ := M.exists_isBasis A
  have hJfin : J.Finite := hE.subset hJA.indep.subset_ground
  have hJK : J ⊆ K := hJA.subset.trans hAK
  have hJrank : M.eRk J = (3 : ℕ∞) := by
    rw [hJA.eRk_eq_eRk, hArank]
  have hJBasisK : M.IsBasis J K :=
    hJA.indep.isBasis_of_eRk_ge hJfin hJK
      (by rw [hK.2.1, hJrank])
  have hgNonloop : M.IsNonloop g :=
    isNonloop_of_strict_rankFour hRank hStrict
      (hH.subset_ground hg.1)
  have hgK : ({g} : Set α) ⊆ K := by simpa using hg.2
  obtain ⟨I, hIK, hgI, hIJ⟩ :=
    hgNonloop.indep.exists_isBasis_subset_union_isBasis hgK hJBasisK
  have hIfin : I.Finite := hE.subset hIK.indep.subset_ground
  have hIncard : I.ncard = 3 := by
    have henc : I.encard = (3 : ℕ∞) := by
      rw [hIK.encard_eq_eRk, hK.2.1]
    rw [← hIfin.cast_ncard_eq] at henc
    exact_mod_cast henc
  have hgmem : g ∈ I := hgI (by simp)
  let R : Set α := I \ {g}
  have hRfin : R.Finite := hIfin.sdiff
  have hRcard : R.ncard = 2 := by
    have h := Set.ncard_sdiff_singleton_add_one hgmem hIfin
    dsimp [R]
    rw [hIncard] at h
    omega
  obtain ⟨x, y, hxy, hRpair⟩ := Set.ncard_eq_two.mp hRcard
  have hxR : x ∈ R := by rw [hRpair]; simp
  have hyR : y ∈ R := by rw [hRpair]; simp
  have hRsubJ : R ⊆ J := by
    intro z hz
    have hzI : z ∈ I := hz.1
    have hzne : z ≠ g := by simpa using hz.2
    have hzU := hIJ hzI
    rcases hzU with hzg | hzJ
    · exact (hzne (by simpa using hzg)).elim
    · exact hzJ
  have hxA : x ∈ A := hJA.subset (hRsubJ hxR)
  have hyA : y ∈ A := hJA.subset (hRsubJ hyR)
  have hIeq : I = insert g R := by
    rw [Set.insert_sdiff_self_of_mem hgmem]
  refine ⟨x, y, ?_, ?_, hxy, ?_⟩
  · simpa [A] using hxA
  · simpa [A] using hyA
  · rw [hIeq, hRpair] at hIK
    simpa [Set.pair_comm] using hIK

/-- For either possible side rank, there is a bad subset of the rank-two core
of size at most k-1 outside of which every core element has a side witness. -/
theorem dangerous_two_exists_small_bad_set
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K) :
    ∃ Bad : Set α,
      Bad ⊆ H ∩ K ∧ Bad.ncard ≤ k - 1 ∧
      ∀ g ∈ H ∩ K, g ∉ Bad →
        ∃ x y : α, x ∈ M.E \ H ∧ y ∈ M.E \ H ∧ x ≠ y ∧
          M.IsBasis ({g, x, y} : Set α) K := by
  rcases dangerous_two_complement_rank_two_or_three
      hk hE hRank hEcard hStrict hH hK hne with hA2 | hA3
  · let Bad : Set α := (H ∩ K) ∩ M.closure (M.E \ H)
    refine ⟨Bad, Set.inter_subset_left, ?_, ?_⟩
    · dsimp [Bad]
      exact dangerous_two_core_inter_complement_closure_ncard_le
        hk hE hRank hEcard hStrict hH hK hne hA2
    · intro g hg hgbad
      have hgcl : g ∉ M.closure (M.E \ H) := by
        intro h
        exact hgbad ⟨hg, h⟩
      exact dangerous_two_rankTwo_side_good_of_not_mem_closure
        hk hE hRank hEcard hStrict hH hK hne hg hA2 hgcl
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro g hg hgbad
    exact dangerous_two_rankThree_side_good
      hk hE hRank hEcard hStrict hH hK hne hg hA3

end

end Rank4DangerousBranches
end HigherRankKUM
