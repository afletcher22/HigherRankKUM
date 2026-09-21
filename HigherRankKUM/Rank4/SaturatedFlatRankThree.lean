import HigherRankKUM.StrictDensity
import HigherRankKUM.LowRank.RankThree

namespace HigherRankKUM
namespace Rank4SaturatedFlatRankThree

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- A rank-three subset of cardinality 3k inside a strict rank-four
(4k+2)/4 instance is uniformly dense at the integral rank-three density k.

The only nontrivial rank layers are one and two. Strict ambient density gives
|A| <= k in rank one and |A| <= 2k in rank two by integer rounding. Rank
three is bounded by containment in H itself. -/
theorem uniformlyDense_restrict_of_rankThree_ncard_three_mul
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hHsub : H ⊆ M.E)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (hHcard : H.ncard = 3 * k) :
    UniformlyDense (M ↾ H) k := by
  have hHfin : H.Finite := hGroundFin.subset hHsub
  have hHproper : H ≠ M.E := by
    intro hEq
    have hr := hHrank
    rw [hEq, M.eRk_ground, hRank] at hr
    norm_num at hr
  intro A hA
  have hAH : A ⊆ H := by
    simpa using hA
  have hAE : A ⊆ M.E := hAH.trans hHsub
  have hAfin : A.Finite := hGroundFin.subset hAE
  rw [M.restrict_eRk_eq hAH]
  by_cases hAempty : A = ∅
  · subst A
    simp
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
  have hAproper : A ≠ M.E := by
    intro hEq
    apply hHproper
    apply Set.Subset.antisymm hHsub
    rw [← hEq]
    exact hAH
  have hRle : M.eRk A ≤ (3 : ℕ∞) := by
    calc
      M.eRk A ≤ M.eRk H := M.eRk_mono hAH
      _ = (3 : ℕ∞) := hHrank
  obtain ⟨j, hAj, hjle⟩ := ENat.le_natCast_iff.mp hRle
  have hjleNat : j ≤ 3 := by
    exact_mod_cast hjle
  have hs := hStrict A hAE hAne hAproper
  rw [← hAfin.cast_ncard_eq, hAj] at hs
  have hsNat :
      4 * A.ncard < (4 * k + 2) * j := by
    exact_mod_cast hs
  have hcardH : A.ncard ≤ 3 * k := by
    calc
      A.ncard ≤ H.ncard := Set.ncard_le_ncard hAH hHfin
      _ = 3 * k := hHcard
  have hNat : A.ncard ≤ k * j := by
    interval_cases j <;> omega
  rw [hAj, ← hAfin.cast_ncard_eq]
  exact_mod_cast hNat

/-- Consequently every saturated rank-three subset carries a rank-three CBO.

This is the direct bridge from the rank-four saturation program to the frozen
Rank3KUM theorem. -/
theorem exists_cyclicBasisOrder_restrict_of_rankThree_ncard_three_mul
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 0 < k)
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hHsub : H ⊆ M.E)
    (hHrank : M.eRk H = (3 : ℕ∞))
    (hHcard : H.ncard = 3 * k) :
    ∃ order : Fin (3 * k) ≃ (M ↾ H).E,
      CyclicBasisOrder (M ↾ H) 3 (by omega) order := by
  have hHfin : H.Finite := hGroundFin.subset hHsub
  have hDense :
      UniformlyDense (M ↾ H) k :=
    uniformlyDense_restrict_of_rankThree_ncard_three_mul
      hGroundFin hRank hStrict hHsub hHrank hHcard
  apply exists_cyclicBasisOrder_of_rank_three (M ↾ H) k hk
  · simpa using hHfin
  · simpa using hHrank
  · rw [Matroid.restrict_ground_eq, ← hHfin.cast_ncard_eq, hHcard]
  · exact hDense

end

end Rank4SaturatedFlatRankThree
end HigherRankKUM
