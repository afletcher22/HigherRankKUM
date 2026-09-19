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

end

end Rank4DangerousBranches
end HigherRankKUM
