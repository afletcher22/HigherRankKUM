import HigherRankKUM.Rank4.DangerousBranchFactors

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- The complement of one dangerous hyperplane lies inside every other
distinct dangerous hyperplane. -/
theorem dangerous_complement_subset_other
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K) :
    M.E \ H ⊆ K := by
  have hd :
      Disjoint (M.E \ H) (M.E \ K) :=
    dangerous_complements_disjoint
      hE hRank hEcard hStrict hH hK hne
  intro x hx
  by_contra hxK
  exact (Set.disjoint_left.1 hd) hx ⟨hx.1, hxK⟩

/-- For three distinct dangerous hyperplanes, the complement of one together
with the triple core is exactly the intersection of the other two. -/
theorem dangerous_triple_core_union_complement
    {M : Matroid α} {k : ℕ} {H₀ H₁ H₂ : Set α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hH₂ : DangerousHyperplane M k H₂)
    (h01 : H₀ ≠ H₁) (h02 : H₀ ≠ H₂) (h12 : H₁ ≠ H₂) :
    ((H₀ ∩ H₁) ∩ H₂) ∪ (M.E \ H₀) = H₁ ∩ H₂ := by
  have hA1 : M.E \ H₀ ⊆ H₁ :=
    dangerous_complement_subset_other
      hE hRank hEcard hStrict hH₀ hH₁ h01
  have hA2 : M.E \ H₀ ⊆ H₂ :=
    dangerous_complement_subset_other
      hE hRank hEcard hStrict hH₀ hH₂ h02
  ext x
  constructor
  · rintro (hxG | hxA)
    · exact ⟨hxG.1.2, hxG.2⟩
    · exact ⟨hA1 hxA, hA2 hxA⟩
  · intro hx
    by_cases hx0 : x ∈ H₀
    · exact Or.inl ⟨⟨hx0, hx.1⟩, hx.2⟩
    · have hxE : x ∈ M.E := hH₁.subset_ground hx.1
      exact Or.inr ⟨hxE, hx0⟩

/-- In the three-dangerous-hyperplane branch, each complement side class has
ambient rank exactly two. -/
theorem dangerous_triple_complement_eRk_eq_two
    {M : Matroid α} {k : ℕ} {H₀ H₁ H₂ : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hH₂ : DangerousHyperplane M k H₂)
    (h01 : H₀ ≠ H₁) (h02 : H₀ ≠ H₂) (h12 : H₁ ≠ H₂) :
    M.eRk (M.E \ H₀) = (2 : ℕ∞) := by
  let A : Set α := M.E \ H₀
  have hA1 : A ⊆ H₁ := by
    dsimp [A]
    exact dangerous_complement_subset_other
      hE hRank hEcard hStrict hH₀ hH₁ h01
  have hA2 : A ⊆ H₂ := by
    dsimp [A]
    exact dangerous_complement_subset_other
      hE hRank hEcard hStrict hH₀ hH₂ h02
  have hAsubI : A ⊆ H₁ ∩ H₂ := fun x hx => ⟨hA1 hx, hA2 hx⟩
  have hIrank : M.eRk (H₁ ∩ H₂) = (2 : ℕ∞) :=
    dangerous_inter_eRk_eq_two
      hk hE hRank hEcard hStrict hH₁ hH₂ h12
  have hArankLe : M.eRk A ≤ (2 : ℕ∞) := by
    calc
      M.eRk A ≤ M.eRk (H₁ ∩ H₂) := M.eRk_mono hAsubI
      _ = (2 : ℕ∞) := hIrank
  have hAfin : A.Finite := by
    dsimp [A]
    exact hE.sdiff
  have hAcard : A.ncard = k + 1 := by
    dsimp [A]
    exact dangerous_complement_ncard_eq hE hEcard hH₀
  have hAnonempty : A.Nonempty := by
    rw [← Set.ncard_pos hAfin, hAcard]
    omega
  have hAproper : A ≠ M.E := by
    intro hEq
    have hle := hArankLe
    rw [hEq, M.eRk_ground, hRank] at hle
    norm_num at hle
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hArankLe
  have hjleNat : j ≤ 2 := by
    exact_mod_cast hjle
  have hs := hStrict A (by
    dsimp [A]
    exact Set.sdiff_subset) hAnonempty hAproper
  rw [← hAfin.cast_ncard_eq, hAcard, hj] at hs
  have hsNat : 4 * (k + 1) < (4 * k + 2) * j := by
    exact_mod_cast hs
  have hj2 : j = 2 := by
    interval_cases j <;> omega
  dsimp [A] at hj
  simpa [hj2] using hj

/-- The rank-two flat attached to a side class is exactly the union of that
side with the triple core. -/
theorem dangerous_triple_side_core_flat
    {M : Matroid α} {k : ℕ} {H₀ H₁ H₂ : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hH₂ : DangerousHyperplane M k H₂)
    (h01 : H₀ ≠ H₁) (h02 : H₀ ≠ H₂) (h12 : H₁ ≠ H₂) :
    M.IsFlat (((H₀ ∩ H₁) ∩ H₂) ∪ (M.E \ H₀)) ∧
      M.eRk (((H₀ ∩ H₁) ∩ H₂) ∪ (M.E \ H₀)) = (2 : ℕ∞) := by
  rw [dangerous_triple_core_union_complement
    hE hRank hEcard hStrict hH₀ hH₁ hH₂ h01 h02 h12]
  exact ⟨isFlat_inter_of_isFlat hH₁.1 hH₂.1,
    dangerous_inter_eRk_eq_two
      hk hE hRank hEcard hStrict hH₁ hH₂ h12⟩


/-- Generic rank-four nested-flat extension lemma used by all three dangerous
branches.  A rank-two basis inside a rank-two flat, one new element in a
containing rank-three flat, and one element outside that hyperplane form an
ambient basis. -/
theorem isBase_of_rankTwo_basis_nested_rankThree
    {M : Matroid α} {I F H : Set α} {b c : α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hI : M.Indep I) (hIfin : I.Finite)
    (hIRank : M.eRk I = (2 : ℕ∞))
    (hIF : I ⊆ F)
    (hFflat : M.IsFlat F) (hFrank : M.eRk F = (2 : ℕ∞))
    (hFH : F ⊆ H)
    (hHflat : M.IsFlat H) (hHrank : M.eRk H = (3 : ℕ∞))
    (hbH : b ∈ H) (hbF : b ∉ F)
    (hcE : c ∈ M.E) (hcH : c ∉ H) :
    M.IsBase (insert c (insert b I)) := by
  have hBasisF : M.IsBasis I F :=
    hI.isBasis_of_eRk_ge hIfin hIF (by rw [hFrank, hIRank])
  have hclI : M.closure I = F := by
    rw [hBasisF.closure_eq_closure, hFflat.closure]
  have hbE : b ∈ M.E := hHflat.subset_ground hbH
  have hbI : b ∉ I := by
    intro hb
    exact hbF (hIF hb)
  have hbcl : b ∉ M.closure I := by
    rwa [hclI]
  have hJ : M.Indep (insert b I) :=
    (hI.insert_indep_iff_of_notMem hbI).2 ⟨hbE, hbcl⟩
  have hJfin : (insert b I).Finite := hIfin.insert b
  have hJH : insert b I ⊆ H := by
    intro x hx
    rcases hx with rfl | hx
    · exact hbH
    · exact hFH (hIF hx)
  have hJrank : M.eRk (insert b I) = (3 : ℕ∞) := by
    rw [M.eRk_insert_eq_add_one ⟨hbE, hbcl⟩, hIRank]
    norm_num
  have hBasisH : M.IsBasis (insert b I) H :=
    hJ.isBasis_of_eRk_ge hJfin hJH (by rw [hHrank, hJrank])
  have hclJ : M.closure (insert b I) = H := by
    rw [hBasisH.closure_eq_closure, hHflat.closure]
  have hcJ : c ∉ insert b I := by
    intro hc
    exact hcH (hJH hc)
  have hccl : c ∉ M.closure (insert b I) := by
    rwa [hclJ]
  have hK : M.Indep (insert c (insert b I)) :=
    (hJ.insert_indep_iff_of_notMem hcJ).2 ⟨hcE, hccl⟩
  have hKrank : M.eRk (insert c (insert b I)) = (4 : ℕ∞) := by
    rw [M.eRk_insert_eq_add_one ⟨hcE, hccl⟩, hJrank]
    norm_num
  exact hK.isBase_of_eRk_ge (hJfin.insert c) (by rw [hRank, hKrank])

/-- In a strict rank-four `4k+2` instance, every ground element is a nonloop.
This local strict-density version avoids introducing a separate weak-density
conversion just to use singleton closure. -/
theorem isNonloop_of_strict_rankFour
    {M : Matroid α} {k : ℕ} {e : α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (heE : e ∈ M.E) :
    M.IsNonloop e := by
  have hsingleSub : ({e} : Set α) ⊆ M.E := by simpa using heE
  have hsingleProper : ({e} : Set α) ≠ M.E := by
    intro hEq
    have hr := M.eRk_le_encard ({e} : Set α)
    rw [hEq, M.eRk_ground, hRank, Set.encard_singleton] at hr
    norm_num at hr
  have hs := hStrict ({e} : Set α) hsingleSub (by simp) hsingleProper
  have hne0 : M.eRk ({e} : Set α) ≠ 0 := by
    intro hzero
    rw [Set.encard_singleton, hzero] at hs
    simp at hs
  have hle1 : M.eRk ({e} : Set α) ≤ (1 : ℕ∞) := M.eRk_singleton_le e
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hle1
  have hjleNat : j ≤ 1 := by exact_mod_cast hjle
  have hj1 : j = 1 := by
    by_contra hjne
    have hj0 : j = 0 := by omega
    exact hne0 (by simpa [hj0] using hj)
  rw [Matroid.eRk_singleton_eq_one_iff]
  simpa [hj1] using hj

/-- A triple-core element and an element of one complementary side form an
independent pair.  The core is a rank-one flat, while the side lies outside
the dangerous hyperplane defining that complement. -/
theorem dangerous_triple_core_side_pair_indep
    {M : Matroid α} {k : ℕ} {H₀ H₁ H₂ : Set α} {g a : α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hH₂ : DangerousHyperplane M k H₂)
    (h01 : H₀ ≠ H₁) (h02 : H₀ ≠ H₂) (h12 : H₁ ≠ H₂)
    (hg : g ∈ (H₀ ∩ H₁) ∩ H₂)
    (ha : a ∈ M.E \ H₀) :
    M.Indep ({g, a} : Set α) := by
  let G : Set α := (H₀ ∩ H₁) ∩ H₂
  have hG := dangerous_triple_core
    hk hE hRank hEcard hStrict hH₀ hH₁ hH₂ h01 h02 h12
  have hGflat : M.IsFlat G := by simpa [G] using hG.1
  have hGrank : M.eRk G = (1 : ℕ∞) := by simpa [G] using hG.2.1
  have hgG : g ∈ G := by simpa [G] using hg
  have hgNonloop : M.IsNonloop g :=
    isNonloop_of_strict_rankFour hRank hStrict
      (hGflat.subset_ground hgG)
  have hgBasis : M.IsBasis ({g} : Set α) G := by
    apply hgNonloop.indep.isBasis_of_eRk_ge (by simp)
      (by simpa using hgG)
    rw [hGrank, hgNonloop.eRk_eq]
  have hclg : M.closure ({g} : Set α) = G := by
    rw [hgBasis.closure_eq_closure, hGflat.closure]
  have haG : a ∉ G := by
    intro haG
    exact ha.2 haG.1.1
  have hag : a ≠ g := by
    intro h
    subst a
    exact haG hgG
  rw [← Set.insert_singleton_eq]
  exact (hgNonloop.indep.insert_indep_iff_of_notMem (by simpa [hag])).2
    ⟨ha.1, by rwa [hclg]⟩

/-- The basic `t=3` window certificate: two distinct independent elements
from one side class, together with one element from each of the other two
side classes, form a basis. -/
theorem dangerous_triple_side_pair_isBase
    {M : Matroid α} {k : ℕ} {H₀ H₁ H₂ : Set α}
    {x y b c : α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hH₂ : DangerousHyperplane M k H₂)
    (h01 : H₀ ≠ H₁) (h02 : H₀ ≠ H₂) (h12 : H₁ ≠ H₂)
    (hx : x ∈ M.E \ H₀) (hy : y ∈ M.E \ H₀)
    (hxy : x ≠ y) (hpair : M.Indep ({x, y} : Set α))
    (hb : b ∈ M.E \ H₁)
    (hc : c ∈ M.E \ H₂) :
    M.IsBase ({x, y, b, c} : Set α) := by
  let F : Set α := H₁ ∩ H₂
  have hFflat : M.IsFlat F := by
    dsimp [F]
    exact isFlat_inter_of_isFlat hH₁.1 hH₂.1
  have hFrank : M.eRk F = (2 : ℕ∞) := by
    dsimp [F]
    exact dangerous_inter_eRk_eq_two
      hk hE hRank hEcard hStrict hH₁ hH₂ h12
  have hA1 : M.E \ H₀ ⊆ H₁ :=
    dangerous_complement_subset_other
      hE hRank hEcard hStrict hH₀ hH₁ h01
  have hA2 : M.E \ H₀ ⊆ H₂ :=
    dangerous_complement_subset_other
      hE hRank hEcard hStrict hH₀ hH₂ h02
  have hIF : ({x, y} : Set α) ⊆ F := by
    intro z hz
    rcases hz with rfl | hz
    · exact ⟨hA1 hx, hA2 hx⟩
    · have : z = y := by simpa using hz
      subst z
      exact ⟨hA1 hy, hA2 hy⟩
  have hIRank : M.eRk ({x, y} : Set α) = (2 : ℕ∞) := by
    rw [hpair.eRk_eq_encard, Set.encard_pair hxy]
  have hbH₂ : b ∈ H₂ :=
    dangerous_complement_subset_other
      hE hRank hEcard hStrict hH₁ hH₂ h12 hb
  have hbF : b ∉ F := by
    intro hbf
    exact hb.2 hbf.1
  have hraw := isBase_of_rankTwo_basis_nested_rankThree
    (M := M) (I := ({x, y} : Set α)) (F := F) (H := H₂)
    (b := b) (c := c)
    hRank hpair (by simp) hIRank hIF hFflat hFrank
    Set.inter_subset_right hH₂.1 hH₂.2.1
    hbH₂ hbF hc.1 hc.2
  simpa [F, Set.pair_comm] using hraw


end

end Rank4DangerousBranches
end HigherRankKUM
