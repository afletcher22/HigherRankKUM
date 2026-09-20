import HigherRankKUM.Rank4.T0Deletion

namespace HigherRankKUM
namespace Rank4GcdTwoDeletion

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- Rank-four `4k+1` arithmetic has enough residue slack that every
single deletion preserves uniform density at the integral ratio `4k/4`. -/
theorem uniformlyDenseRatio_delete_of_four_mul_add_one
    {M : Matroid α} {k : ℕ}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 1 : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M (4 * k + 1) 4)
    {e : α} (he : e ∈ M.E) :
    UniformlyDenseRatio (M ＼ ({e} : Set α)) (4 * k) 4 := by
  intro X hXdel
  have hXsub : X ⊆ M.E \ ({e} : Set α) := by
    simpa [Matroid.delete_ground] using hXdel
  have hXE : X ⊆ M.E := hXsub.trans Set.sdiff_subset
  have hXfin : X.Finite := hE.subset hXE
  have hDeleteRank :
      (M ＼ ({e} : Set α)).eRk X = M.eRk X := by
    simpa [Matroid.delete_eq_restrict] using
      M.restrict_eRk_eq hXsub
  have hRkBound : M.eRk X ≤ (4 : ℕ∞) := by
    rw [← hRank]
    exact M.eRk_le_eRank X
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRkBound
  have hjleNat : j ≤ 4 := by
    exact_mod_cast hjle
  have hd := hDense X hXE
  rw [← hXfin.cast_ncard_eq, hj] at hd
  have hdNat : 4 * X.ncard ≤ (4 * k + 1) * j := by
    exact_mod_cast hd
  have htargetNat : 4 * X.ncard ≤ (4 * k) * j := by
    by_cases hjlt : j < 4
    · have hjle3 : j ≤ 3 := by omega
      have hsplit :
          (4 * k + 1) * j = 4 * (k * j) + j := by
        ring
      have htargetForm :
          (4 * k) * j = 4 * (k * j) := by
        ring
      rw [hsplit] at hdNat
      rw [htargetForm]
      omega
    · have hjEq : j = 4 := by omega
      subst j
      have hEn : M.E.ncard = 4 * k + 1 := by
        have h := hEcard
        rw [← hE.cast_ncard_eq] at h
        exact_mod_cast h
      have hDelCard :
          (M.E \ ({e} : Set α)).ncard = 4 * k := by
        rw [Set.ncard_sdiff_singleton_of_mem he, hEn]
        omega
      have hXcard :
          X.ncard ≤ 4 * k := by
        calc
          X.ncard ≤ (M.E \ ({e} : Set α)).ncard :=
            Set.ncard_le_ncard hXsub hE.sdiff
          _ = 4 * k := hDelCard
      omega
  rw [hDeleteRank, hj, ← hXfin.cast_ncard_eq]
  exact_mod_cast htargetNat

/-- In the strict `t=0` branch, every ordered pair of distinct ground
elements can be deleted successively while preserving the correct density
inequality.  This is the formal two-deletion robustness property used by the
favorable deletion-CBO program. -/
theorem two_deletions_uniformlyDenseRatio_of_no_dangerous
    {M : Matroid α} {k : ℕ}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous : ∀ H : Set α, ¬ DangerousHyperplane M k H)
    {e f : α} (he : e ∈ M.E) (hf : f ∈ M.E) (hef : e ≠ f) :
    UniformlyDenseRatio
      ((M ＼ ({e} : Set α)) ＼ ({f} : Set α)) (4 * k) 4 := by
  obtain ⟨hCard, hRankDel, hDenseDel⟩ :=
    delete_package_of_no_dangerous
      hk hE hRank hEcard hStrict hNoDangerous he
  have hEdel : (M ＼ ({e} : Set α)).E.Finite := by
    rw [Matroid.delete_ground]
    exact hE.sdiff
  have hfDel : f ∈ (M ＼ ({e} : Set α)).E := by
    rw [Matroid.delete_ground]
    refine ⟨hf, ?_⟩
    simp only [Set.mem_singleton_iff]
    exact Ne.symm hef
  exact uniformlyDenseRatio_delete_of_four_mul_add_one
    hk hEdel hRankDel hCard hDenseDel hfDel

end

end Rank4GcdTwoDeletion
end HigherRankKUM
