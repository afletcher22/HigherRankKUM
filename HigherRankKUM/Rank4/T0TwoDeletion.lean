import HigherRankKUM.Rank4.T0Deletion

namespace HigherRankKUM
namespace Rank4GcdTwoDeletion

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- In the strict rank-four \`4k+2\`, \`t=0\` branch, every rank-at-most-three
set has at most \`3k\` elements. The only strict-density extremal possibility
would have size \`3k+1\`; its closure would then be a dangerous hyperplane. -/
theorem ncard_le_three_mul_of_no_dangerous
    {M : Matroid α} {k : ℕ}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous : ∀ H : Set α, ¬ DangerousHyperplane M k H)
    {X : Set α}
    (hX : X ⊆ M.E)
    (hRk : M.eRk X ≤ (3 : ℕ∞)) :
    X.ncard ≤ 3 * k := by
  by_cases hXempty : X = ∅
  · simp [hXempty]
  have hXnonempty : X.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hXempty
  have hXproper : X ≠ M.E := by
    intro hEq
    have hr := hRk
    rw [hEq, M.eRk_ground, hRank] at hr
    norm_num at hr
  have hXfin : X.Finite := hE.subset hX
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRk
  have hjleNat : j ≤ 3 := by exact_mod_cast hjle
  have hs := hStrict X hX hXnonempty hXproper
  rw [← hXfin.cast_ncard_eq, hj] at hs
  have hsNat : 4 * X.ncard < (4 * k + 2) * j := by
    exact_mod_cast hs
  have hmul :
      (4 * k + 2) * j ≤ (4 * k + 2) * 3 :=
    Nat.mul_le_mul_left (4 * k + 2) hjleNat
  have hcap : X.ncard ≤ 3 * k + 1 := by
    have hlt := hsNat.trans_le hmul
    omega
  by_contra hnot
  have hXcard : X.ncard = 3 * k + 1 := by
    omega
  have hj3 : j = 3 := by
    interval_cases j <;> omega
  subst j
  have hXrank : M.eRk X = (3 : ℕ∞) := by
    simpa using hj
  have hXflat : M.IsFlat X := by
    rw [Matroid.isFlat_iff_closure_eq]
    apply Set.Subset.antisymm
    · have hclSub : M.closure X ⊆ M.E :=
        M.closure_subset_ground X
      have hclFin : (M.closure X).Finite :=
        hE.subset hclSub
      by_contra hnotSub
      have hneClosure : X ≠ M.closure X := by
        intro hEq
        apply hnotSub
        rw [← hEq]
      have hss : X ⊂ M.closure X :=
        (M.subset_closure X hX).ssubset_of_ne hneClosure
      have hcardLt : X.ncard < (M.closure X).ncard :=
        Set.ncard_lt_ncard hss hclFin
      have hclNonempty : (M.closure X).Nonempty :=
        hXnonempty.mono (M.subset_closure X hX)
      have hclProper : M.closure X ≠ M.E := by
        intro hEq
        have hr := M.eRk_closure_eq X
        rw [hEq, M.eRk_ground, hRank, hXrank] at hr
        norm_num at hr
      have hscl := hStrict (M.closure X) hclSub hclNonempty hclProper
      rw [← hclFin.cast_ncard_eq, M.eRk_closure_eq, hXrank] at hscl
      have hsclNat :
          4 * (M.closure X).ncard < (4 * k + 2) * 3 := by
        exact_mod_cast hscl
      omega
    · exact M.subset_closure X hX
  have hXencard : X.encard = ((3 * k + 1 : ℕ) : ℕ∞) := by
    rw [← hXfin.cast_ncard_eq, hXcard]
  exact hNoDangerous X ⟨hXflat, hXrank, hXencard⟩

/-- Two-deletion robustness of the strict \`t=0\` rank-four gcd-two branch.

For \`k ≥ 2\`, deleting an arbitrary two-element subset preserves ground size
\`4k\`, rank four, and uniform density at ratio \`4k/4\`. -/
theorem delete_two_package_of_no_dangerous
    {M : Matroid α} {k : ℕ} {D : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous : ∀ H : Set α, ¬ DangerousHyperplane M k H)
    (hDsub : D ⊆ M.E)
    (hDcard : D.ncard = 2) :
    (M ＼ D).E.encard = ((4 * k : ℕ) : ℕ∞) ∧
    (M ＼ D).eRank = (4 : ℕ∞) ∧
    UniformlyDenseRatio (M ＼ D) (4 * k) 4 := by
  have hDfin : D.Finite := hE.subset hDsub
  have hDnonempty : D.Nonempty := by
    rw [← Set.ncard_pos hDfin, hDcard]
    omega
  let R := M.E \ D
  have hRsub : R ⊆ M.E := Set.sdiff_subset
  have hRfin : R.Finite := hE.subset hRsub
  have hEn : M.E.ncard = 4 * k + 2 := by
    have h := hEcard
    rw [← hE.cast_ncard_eq] at h
    exact_mod_cast h
  have hRcard : R.ncard = 4 * k := by
    dsimp [R]
    rw [Set.ncard_sdiff' hDsub hE, hEn, hDcard]
    omega
  have hRnonempty : R.Nonempty := by
    rw [← Set.ncard_pos hRfin, hRcard]
    omega
  have hRproper : R ≠ M.E := by
    intro hEq
    obtain ⟨d, hdD⟩ := hDnonempty
    have hdE : d ∈ M.E := hDsub hdD
    have hdR : d ∈ R := by
      rw [hEq]
      exact hdE
    exact hdR.2 hdD
  have hSpan : M.Spanning R := by
    by_contra hnotspan
    have hRankLt : M.eRk R < M.eRank := by
      have hnotle : ¬ M.eRank ≤ M.eRk R := by
        intro hle
        exact hnotspan ((M.spanning_iff_eRk_le hRsub).2 hle)
      exact lt_of_not_ge hnotle
    rw [hRank] at hRankLt
    obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRankLt.le
    have hjleNat : j ≤ 3 := by
      have hjlt : j < 4 := by
        rw [hj] at hRankLt
        exact_mod_cast hRankLt
      omega
    have hs := hStrict R hRsub hRnonempty hRproper
    rw [← hRfin.cast_ncard_eq, hj, hRcard] at hs
    have hsNat : 4 * (4 * k) < (4 * k + 2) * j := by
      exact_mod_cast hs
    have hupper :
        (4 * k + 2) * j ≤ (4 * k + 2) * 3 :=
      Nat.mul_le_mul_left (4 * k + 2) hjleNat
    omega
  have hdelRank :
      (M ＼ D).eRank = M.eRank := by
    simpa [Matroid.delete_eq_restrict, R] using hSpan.eRank_restrict
  have hdelCard :
      (M ＼ D).E.encard = ((4 * k : ℕ) : ℕ∞) := by
    rw [Matroid.delete_ground]
    have hdiff : (M.E \ D).ncard = 4 * k := by
      simpa [R] using hRcard
    rw [← (hE.sdiff).cast_ncard_eq, hdiff]
  refine ⟨hdelCard, ?_, ?_⟩
  · simpa [hRank] using hdelRank
  · intro X hXdel
    have hXsub : X ⊆ M.E \ D := by
      simpa [Matroid.delete_ground] using hXdel
    have hXE : X ⊆ M.E := hXsub.trans Set.sdiff_subset
    have hXfin : X.Finite := hE.subset hXE
    have hRkDel :
        (M ＼ D).eRk X = M.eRk X := by
      simpa [Matroid.delete_eq_restrict] using
        M.restrict_eRk_eq hXsub
    have hRkBound : M.eRk X ≤ (4 : ℕ∞) := by
      rw [← hRank]
      exact M.eRk_le_eRank X
    obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRkBound
    rw [hRkDel, hj, ← hXfin.cast_ncard_eq]
    by_cases hXempty : X = ∅
    · simp [hXempty]
    have hs := hStrict X hXE
      (Set.nonempty_iff_ne_empty.mpr hXempty)
      (by
        intro hEq
        obtain ⟨d, hdD⟩ := hDnonempty
        have hdX : d ∈ X := by
          rw [hEq]
          exact hDsub hdD
        exact (hXsub hdX).2 hdD)
    rw [← hXfin.cast_ncard_eq, hj] at hs
    have hsNat : 4 * X.ncard < (4 * k + 2) * j := by
      exact_mod_cast hs
    have hNat : 4 * X.ncard ≤ (4 * k) * j := by
      interval_cases j
      · omega
      · omega
      · omega
      · have hRk3 : M.eRk X ≤ (3 : ℕ∞) := by
          rw [hj]
        have hXcard :=
          ncard_le_three_mul_of_no_dangerous
            hE hRank hStrict hNoDangerous hXE hRk3
        omega
      · have hXcard : X.ncard ≤ 4 * k := by
          have hle : X.ncard ≤ (M.E \ D).ncard :=
            Set.ncard_le_ncard hXsub hE.sdiff
          rw [show (M.E \ D).ncard = 4 * k by simpa [R] using hRcard] at hle
          exact hle
        omega
    exact_mod_cast hNat

end

end Rank4GcdTwoDeletion
end HigherRankKUM
