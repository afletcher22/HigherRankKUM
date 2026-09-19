import HigherRankKUM.Rank4.GcdTwoDeletion

namespace HigherRankKUM
namespace Rank4GcdTwoDeletion

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- In a strict rank-four 4k+2 instance, two distinct dangerous hyperplanes
meet in a rank-two flat. The cardinality 2k and rank-at-most-two statements
are already available in GcdTwoDeletion; strict density rules out rank 0 or 1. -/
theorem dangerous_inter_eRk_eq_two
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K) :
    M.eRk (H ∩ K) = (2 : ℕ∞) := by
  have hRkLe : M.eRk (H ∩ K) ≤ (2 : ℕ∞) :=
    dangerous_inter_eRk_le_two hE hH hK hne
  have hCard : (H ∩ K).ncard = 2 * k :=
    dangerous_inter_ncard_eq_two_mul
      hE hRank hEcard hStrict hH hK hne
  have hSub : H ∩ K ⊆ M.E :=
    Set.inter_subset_left.trans hH.subset_ground
  have hFin : (H ∩ K).Finite := hE.subset hSub
  have hNonempty : (H ∩ K).Nonempty := by
    rw [← Set.ncard_pos hFin, hCard]
    omega
  have hProper : H ∩ K ≠ M.E := by
    intro hEq
    have h := hRkLe
    rw [hEq, M.eRk_ground, hRank] at h
    norm_num at h
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRkLe
  have hjleNat : j ≤ 2 := by
    exact_mod_cast hjle
  have hs := hStrict (H ∩ K) hSub hNonempty hProper
  rw [← hFin.cast_ncard_eq, hCard, hj] at hs
  have hsNat : 4 * (2 * k) < (4 * k + 2) * j := by
    exact_mod_cast hs
  have hj2 : j = 2 := by
    interval_cases j <;> omega
  simpa [hj2] using hj

/-- Three distinct dangerous hyperplanes have a rank-one triple core of
cardinality k-1, for k at least two.

This is the formal structural statement behind the three-line-pencil geometry
of the sharp rank-four family. -/
theorem dangerous_triple_core
    {M : Matroid α} {k : ℕ} {H₀ H₁ H₂ : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hH₂ : DangerousHyperplane M k H₂)
    (h01 : H₀ ≠ H₁) (h02 : H₀ ≠ H₂) (h12 : H₁ ≠ H₂) :
    M.IsFlat ((H₀ ∩ H₁) ∩ H₂) ∧
      M.eRk ((H₀ ∩ H₁) ∩ H₂) = (1 : ℕ∞) ∧
      ((H₀ ∩ H₁) ∩ H₂).ncard = k - 1 := by
  let I : Set α := H₀ ∩ H₁
  let C₂ : Set α := M.E \ H₂
  let G : Set α := I ∩ H₂

  have hIflat : M.IsFlat I := by
    dsimp [I]
    exact isFlat_inter_of_isFlat hH₀.1 hH₁.1
  have hIrank : M.eRk I = (2 : ℕ∞) := by
    dsimp [I]
    exact dangerous_inter_eRk_eq_two
      (k := k) (H := H₀) (K := H₁)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict hH₀ hH₁ h01
  have hIcard : I.ncard = 2 * k := by
    dsimp [I]
    exact dangerous_inter_ncard_eq_two_mul
      hE hRank hEcard hStrict hH₀ hH₁ h01
  have hIsub : I ⊆ M.E :=
    Set.inter_subset_left.trans hH₀.subset_ground
  have hIfin : I.Finite := hE.subset hIsub
  have hIproper : I ≠ M.E := by
    intro hEq
    have hr := hIrank
    rw [hEq, M.eRk_ground, hRank] at hr
    norm_num at hr

  have hC₂fin : C₂.Finite := by
    dsimp [C₂]
    exact hE.sdiff
  have hC₂card : C₂.ncard = k + 1 := by
    dsimp [C₂]
    exact dangerous_complement_ncard_eq hE hEcard hH₂
  have hd20 : Disjoint C₂ (M.E \ H₀) := by
    dsimp [C₂]
    exact dangerous_complements_disjoint
      hE hRank hEcard hStrict hH₂ hH₀ h02.symm
  have hd21 : Disjoint C₂ (M.E \ H₁) := by
    dsimp [C₂]
    exact dangerous_complements_disjoint
      hE hRank hEcard hStrict hH₂ hH₁ h12.symm
  have hC₂subI : C₂ ⊆ I := by
    intro x hx
    have hxE : x ∈ M.E := hx.1
    have hxH₀ : x ∈ H₀ := by
      by_contra hxnot
      exact (Set.disjoint_left.mp hd20) hx ⟨hxE, hxnot⟩
    have hxH₁ : x ∈ H₁ := by
      by_contra hxnot
      exact (Set.disjoint_left.mp hd21) hx ⟨hxE, hxnot⟩
    exact ⟨hxH₀, hxH₁⟩

  have hGflat : M.IsFlat G := by
    dsimp [G]
    exact isFlat_inter_of_isFlat hIflat hH₂.1
  have hGsubI : G ⊆ I := Set.inter_subset_left
  have hGsubE : G ⊆ M.E := hGsubI.trans hIsub
  have hGfin : G.Finite := hE.subset hGsubE
  have hGproper : G ≠ M.E := by
    intro hEq
    apply hIproper
    apply Set.Subset.antisymm
    · exact hIsub
    · intro x hxE
      have hxG : x ∈ G := by
        rw [hEq]
        exact hxE
      exact hGsubI hxG

  have hDiff : I \ C₂ = G := by
    ext x
    constructor
    · rintro ⟨hxI, hxnotC⟩
      have hxH₂ : x ∈ H₂ := by
        by_contra hxnotH₂
        exact hxnotC ⟨hIsub hxI, hxnotH₂⟩
      exact ⟨hxI, hxH₂⟩
    · rintro ⟨hxI, hxH₂⟩
      refine ⟨hxI, ?_⟩
      intro hxC
      exact hxC.2 hxH₂
  have hGcard : G.ncard = k - 1 := by
    rw [← hDiff, Set.ncard_sdiff' hC₂subI hIfin, hIcard, hC₂card]
    omega
  have hGnonempty : G.Nonempty := by
    rw [← Set.ncard_pos hGfin, hGcard]
    omega

  have hGrankLe : M.eRk G ≤ (2 : ℕ∞) := by
    rw [← hIrank]
    exact M.eRk_mono hGsubI
  have hGrankNeZero : M.eRk G ≠ (0 : ℕ∞) := by
    intro hzero
    have hs := hStrict G hGsubE hGnonempty hGproper
    rw [← hGfin.cast_ncard_eq, hGcard, hzero] at hs
    have hsNat : 4 * (k - 1) < (4 * k + 2) * 0 := by
      exact_mod_cast hs
    omega
  have hGrankNeTwo : M.eRk G ≠ (2 : ℕ∞) := by
    intro htwo
    have hge : M.eRk I ≤ M.eRk G := by
      rw [hIrank, htwo]
    have hcl :=
      (M.isRkFinite_of_finite hGfin).closure_eq_closure_of_subset_of_eRk_ge_eRk
        hGsubI hge
    have hGI : G = I := by
      rw [hGflat.closure, hIflat.closure] at hcl
      exact hcl
    have hC₂nonempty : C₂.Nonempty := by
      rw [← Set.ncard_pos hC₂fin, hC₂card]
      omega
    obtain ⟨x, hxC₂⟩ := hC₂nonempty
    have hxI : x ∈ I := hC₂subI hxC₂
    have hxG : x ∈ G := by
      rw [hGI]
      exact hxI
    exact hxC₂.2 hxG.2

  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hGrankLe
  have hjleNat : j ≤ 2 := by
    exact_mod_cast hjle
  have hjne0 : j ≠ 0 := by
    intro h
    subst j
    exact hGrankNeZero (by simpa using hj)
  have hjne2 : j ≠ 2 := by
    intro h
    subst j
    exact hGrankNeTwo (by simpa using hj)
  have hj1 : j = 1 := by
    omega
  have hGrank : M.eRk G = (1 : ℕ∞) := by
    simpa [hj1] using hj

  simpa [G, I] using And.intro hGflat (And.intro hGrank hGcard)

end

end Rank4GcdTwoDeletion
end HigherRankKUM
