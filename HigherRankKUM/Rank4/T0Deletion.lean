import HigherRankKUM.Rank4.GcdTwoDeletion

namespace HigherRankKUM
namespace Rank4GcdTwoDeletion

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- If a strict rank-four `4k+2` instance has no dangerous hyperplane,
then every single-element deletion is uniformly dense at ratio `(4k+1)/4`. -/
theorem uniformlyDenseRatio_delete_of_no_dangerous
    {M : Matroid α} {k : ℕ}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous : ∀ H : Set α, ¬ DangerousHyperplane M k H)
    {e : α} (he : e ∈ M.E) :
    UniformlyDenseRatio (M ＼ ({e} : Set α)) (4 * k + 1) 4 := by
  by_contra hbad
  obtain ⟨H, hH, _heH⟩ :=
    (not_uniformlyDenseRatio_delete_iff_exists_dangerous
      hE hRank hStrict he).1 hbad
  exact hNoDangerous H hH

/-- Strict rank-four density on `4k+2` elements (`k ≥ 1`) forbids coloops.
Hence every one-element deletion preserves rank four. -/
theorem not_isColoop_of_strict_gcd_two
    {M : Matroid α} {k : ℕ}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    {e : α} (he : e ∈ M.E) :
    ¬ M.IsColoop e := by
  intro hcol
  let X := M.E \ ({e} : Set α)
  have hXsub : X ⊆ M.E := Set.sdiff_subset
  have hXfin : X.Finite := hE.subset hXsub
  have hEn : M.E.ncard = 4 * k + 2 := by
    have h := hEcard
    rw [← hE.cast_ncard_eq] at h
    exact_mod_cast h
  have hXcard : X.ncard = 4 * k + 1 := by
    dsimp [X]
    rw [Set.ncard_sdiff_singleton_of_mem he, hEn]
    omega
  have hXnonempty : X.Nonempty := by
    rw [← Set.ncard_pos hXfin, hXcard]
    omega
  have hXproper : X ≠ M.E := by
    intro hEq
    have heX : e ∈ X := by
      rw [hEq]
      exact he
    exact heX.2 (by simp)
  letI : M.Finite := ⟨hE⟩
  have hNotSpan : ¬ M.Spanning X := by
    simpa [X] using hcol.sdiff_not_spanning
  have hRankLt : M.eRk X < M.eRank := by
    have hnotle : ¬ M.eRank ≤ M.eRk X := by
      intro hle
      exact hNotSpan ((M.spanning_iff_eRk_le hXsub).2 hle)
    exact lt_of_not_ge hnotle
  rw [hRank] at hRankLt
  obtain ⟨j, hj, _hjle⟩ := ENat.le_natCast_iff.mp hRankLt.le
  have hjlt : j < 4 := by
    rw [hj] at hRankLt
    exact_mod_cast hRankLt
  have hs := hStrict X hXsub hXnonempty hXproper
  rw [← hXfin.cast_ncard_eq, hj, hXcard] at hs
  have hsNat : 4 * (4 * k + 1) < (4 * k + 2) * j := by
    exact_mod_cast hs
  have hUpper : (4 * k + 2) * j ≤ 4 * (4 * k + 1) := by
    omega
  exact (not_lt_of_ge hUpper) hsNat

/-- Exact deletion package for the strict `t=0` gcd-two branch.

If there is no dangerous hyperplane, every ground element can be deleted while
preserving:
* ground size `4k+1`,
* rank four, and
* uniform density at ratio `(4k+1)/4`.

Thus the remaining `t=0` problem is purely a controlled order/lifting problem
after the odd-size deletion is solved. -/
theorem delete_package_of_no_dangerous
    {M : Matroid α} {k : ℕ}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous : ∀ H : Set α, ¬ DangerousHyperplane M k H)
    {e : α} (he : e ∈ M.E) :
    (M ＼ ({e} : Set α)).E.encard = ((4 * k + 1 : ℕ) : ℕ∞) ∧
    (M ＼ ({e} : Set α)).eRank = (4 : ℕ∞) ∧
    UniformlyDenseRatio (M ＼ ({e} : Set α)) (4 * k + 1) 4 := by
  have hnotcol :=
    not_isColoop_of_strict_gcd_two hk hE hRank hEcard hStrict he
  have hspan : M.Spanning (M.E \ ({e} : Set α)) := by
    by_contra hnotspan
    exact hnotcol ((M.isColoop_iff_sdiff_not_spanning).2 hnotspan)
  have hdelRank :
      (M ＼ ({e} : Set α)).eRank = M.eRank := by
    simpa [Matroid.delete_eq_restrict] using hspan.eRank_restrict
  have hdelCard :
      (M ＼ ({e} : Set α)).E.encard = ((4 * k + 1 : ℕ) : ℕ∞) := by
    rw [Matroid.delete_ground]
    have hEn : M.E.ncard = 4 * k + 2 := by
      have h := hEcard
      rw [← hE.cast_ncard_eq] at h
      exact_mod_cast h
    have hdiff :
        (M.E \ ({e} : Set α)).ncard = 4 * k + 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem he, hEn]
      omega
    rw [← (hE.sdiff).cast_ncard_eq, hdiff]
  refine ⟨hdelCard, ?_, ?_⟩
  · simpa [hRank] using hdelRank
  · exact uniformlyDenseRatio_delete_of_no_dangerous
      hE hRank hStrict hNoDangerous he

end

end Rank4GcdTwoDeletion
end HigherRankKUM
