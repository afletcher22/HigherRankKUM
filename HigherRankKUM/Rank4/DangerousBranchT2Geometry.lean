import HigherRankKUM.Rank4.DangerousBranchT3Geometry

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- A basis of a rank-three flat, together with any ground element outside the
flat, is an ambient basis in rank four. -/
theorem isBase_of_rankThree_basis_and_outside
    {M : Matroid α} {I H : Set α} {e : α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hI : M.IsBasis I H)
    (hHflat : M.IsFlat H)
    (heE : e ∈ M.E) (heH : e ∉ H) :
    M.IsBase (insert e I) := by
  have hclI : M.closure I = H := by
    rw [hI.closure_eq_closure, hHflat.closure]
  have heI : e ∉ I := by
    intro he
    exact heH (hI.subset he)
  have hecl : e ∉ M.closure I := by
    rwa [hclI]
  have hInd : M.Indep (insert e I) :=
    (hI.indep.insert_indep_iff_of_notMem heI).2 ⟨heE, hecl⟩
  have hIfin : I.Finite := hI.indep.finite
  have hIrank : M.eRk I = (3 : ℕ∞) := by
    rw [hI.eRk_eq_eRk]
    -- the basis spans the rank-three flat
    have := hHflat
    exact_mod_cast (show (3 : ℕ) = 3 from rfl)
  have hRankInsert : M.eRk (insert e I) = (4 : ℕ∞) := by
    rw [M.eRk_insert_eq_add_one ⟨heE, hecl⟩, hIrank]
    norm_num
  exact hInd.isBase_of_eRk_ge (hIfin.insert e) (by rw [hRank, hRankInsert])

/-- Ordinary `t=2` window certificate.  Two independent core elements,
followed by one element from each dangerous complement, form an ambient
basis. -/
theorem dangerous_two_core_pair_sides_isBase
    {M : Matroid α} {k : ℕ} {H₀ H₁ : Set α}
    {g₀ g₁ a b : α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hne : H₀ ≠ H₁)
    (hg₀ : g₀ ∈ H₀ ∩ H₁) (hg₁ : g₁ ∈ H₀ ∩ H₁)
    (hgne : g₀ ≠ g₁)
    (hpair : M.Indep ({g₀, g₁} : Set α))
    (ha : a ∈ M.E \ H₀)
    (hb : b ∈ M.E \ H₁) :
    M.IsBase ({g₀, g₁, a, b} : Set α) := by
  let G : Set α := H₀ ∩ H₁
  have hGflat : M.IsFlat G := by
    dsimp [G]
    exact isFlat_inter_of_isFlat hH₀.1 hH₁.1
  have hGrank : M.eRk G = (2 : ℕ∞) := by
    dsimp [G]
    exact dangerous_inter_eRk_eq_two
      hk hE hRank hEcard hStrict hH₀ hH₁ hne
  have hpairG : ({g₀, g₁} : Set α) ⊆ G := by
    intro x hx
    rcases hx with rfl | hx
    · exact hg₀
    · simpa using hg₁
  have hpairRank : M.eRk ({g₀, g₁} : Set α) = (2 : ℕ∞) := by
    rw [hpair.eRk_eq_encard, Set.encard_pair hgne]
  have haH₁ : a ∈ H₁ :=
    dangerous_complement_subset_other
      hE hRank hEcard hStrict hH₀ hH₁ hne ha
  have haG : a ∉ G := by
    intro haG
    exact ha.2 haG.1
  have hraw := isBase_of_rankTwo_basis_nested_rankThree
    (M := M) (I := ({g₀, g₁} : Set α)) (F := G) (H := H₁)
    (b := a) (c := b)
    hRank hpair (by simp) hpairRank hpairG hGflat hGrank
    Set.inter_subset_right hH₁.1 hH₁.2.1
    haH₁ haG hb.1 hb.2
  simpa [G, Set.pair_comm] using hraw

/-- Exceptional `t=2` window certificate.  If a core element and two
elements from one side form a basis of the corresponding dangerous
hyperplane, then adding any element from the opposite complement gives an
ambient basis. -/
theorem dangerous_two_hyperplane_triple_plus_other_isBase
    {M : Matroid α} {k : ℕ} {H₀ H₁ : Set α}
    {I : Set α} {a : α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hH₀ : DangerousHyperplane M k H₀)
    (hI : M.IsBasis I H₀)
    (ha : a ∈ M.E \ H₀) :
    M.IsBase (insert a I) :=
  isBase_of_rankThree_basis_and_outside
    hRank hI hH₀.1 ha.1 ha.2

end

end Rank4DangerousBranches
end HigherRankKUM
