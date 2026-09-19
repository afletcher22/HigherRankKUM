import HigherRankKUM.Rank4.DangerousCore
import HigherRankKUM.LowRank.RankTwo
import HigherRankKUM.FullSolver

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- A dangerous rank-three hyperplane of a strict rank-four `4k+2` instance
is uniformly dense at its own exact ratio `(3k+1)/3`.

This is the density input for the `t=1` construction.  Since `3k+1` is
coprime to three, a full rank-three solver (mathematically supplied by the
coprime theorem) gives a cyclic basis ordering of the hyperplane. -/
theorem dangerous_restrict_uniformlyDenseRatio
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H) :
    UniformlyDenseRatio (M.restrict H) (3 * k + 1) 3 := by
  intro X hX
  have hXH : X ⊆ H := by
    simpa using hX
  have hXE : X ⊆ M.E := hXH.trans hH.subset_ground
  by_cases hXempty : X = ∅
  · simp [hXempty]
  have hXnonempty : X.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hXempty
  have hXproper : X ≠ M.E := by
    intro hEq
    apply hH.ne_ground hRank
    apply Set.Subset.antisymm hH.subset_ground
    intro x hxE
    have hxX : x ∈ X := by simpa [hEq] using hxE
    exact hXH hxX
  have hXfin : X.Finite := hE.subset hXE
  have hRkLe : M.eRk X ≤ (3 : ℕ∞) := by
    calc
      M.eRk X ≤ M.eRk H := M.eRk_mono hXH
      _ = (3 : ℕ∞) := hH.2.1
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRkLe
  have hjleNat : j ≤ 3 := by
    exact_mod_cast hjle
  have hs := hStrict X hXE hXnonempty hXproper
  rw [← hXfin.cast_ncard_eq, hj] at hs
  have hsNat : 4 * X.ncard < (4 * k + 2) * j := by
    exact_mod_cast hs
  have hgoalNat : 3 * X.ncard ≤ (3 * k + 1) * j := by
    interval_cases j <;> omega
  rw [M.restrict_eRk_eq hXH, ← hXfin.cast_ncard_eq, hj]
  exact_mod_cast hgoalNat

/-- The intersection of two distinct dangerous hyperplanes is, after
restriction, a uniformly dense rank-two matroid on exactly `2k` elements.

This is the complete lower-rank input used by the direct `t=2` pattern. -/
theorem dangerous_inter_restrict_uniformlyDense
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K) :
    UniformlyDense (M.restrict (H ∩ K)) k := by
  let G : Set α := H ∩ K
  have hGsub : G ⊆ M.E :=
    Set.inter_subset_left.trans hH.subset_ground
  have hGfin : G.Finite := hE.subset hGsub
  have hGrank : M.eRk G = (2 : ℕ∞) := by
    dsimp [G]
    exact dangerous_inter_eRk_eq_two
      hk hE hRank hEcard hStrict hH hK hne
  intro X hX
  have hXG : X ⊆ G := by
    simpa [G] using hX
  have hXE : X ⊆ M.E := hXG.trans hGsub
  by_cases hXempty : X = ∅
  · simp [hXempty]
  have hXnonempty : X.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hXempty
  have hGproper : G ≠ M.E := by
    intro hEq
    have hr := hGrank
    rw [hEq, M.eRk_ground, hRank] at hr
    norm_num at hr
  have hXproper : X ≠ M.E := by
    intro hEq
    apply hGproper
    apply Set.Subset.antisymm hGsub
    intro x hxG
    have hxX : x ∈ X := by simpa [hEq] using hGsub hxG
    exact hXG hxX
  have hXfin : X.Finite := hE.subset hXE
  have hRkLe : M.eRk X ≤ (2 : ℕ∞) := by
    calc
      M.eRk X ≤ M.eRk G := M.eRk_mono hXG
      _ = (2 : ℕ∞) := hGrank
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRkLe
  have hjleNat : j ≤ 2 := by
    exact_mod_cast hjle
  have hs := hStrict X hXE hXnonempty hXproper
  rw [← hXfin.cast_ncard_eq, hj] at hs
  have hsNat : 4 * X.ncard < (4 * k + 2) * j := by
    exact_mod_cast hs
  have hgoalNat : X.ncard ≤ k * j := by
    interval_cases j <;> omega
  rw [M.restrict_eRk_eq hXG, ← hXfin.cast_ncard_eq, hj]
  exact_mod_cast hgoalNat

/-- The rank-two core in the `t=2` branch has an internally certified cyclic
basis ordering. -/
theorem exists_core_cbo_of_two_dangerous
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K) :
    ∃ order : Fin (2 * k) ≃ (M.restrict (H ∩ K)).E,
      CyclicBasisOrder (M.restrict (H ∩ K)) 2 (by omega) order := by
  have hGfin : (H ∩ K).Finite :=
    hE.subset (Set.inter_subset_left.trans hH.subset_ground)
  have hGrank : M.eRk (H ∩ K) = (2 : ℕ∞) :=
    dangerous_inter_eRk_eq_two
      hk hE hRank hEcard hStrict hH hK hne
  have hGcard : (H ∩ K).ncard = 2 * k :=
    dangerous_inter_ncard_eq_two_mul
      hE hRank hEcard hStrict hH hK hne
  have hRestrictFinite : (M.restrict (H ∩ K)).E.Finite := by
    simpa using hGfin
  have hRestrictRank : (M.restrict (H ∩ K)).eRank = (2 : ℕ∞) := by
    simpa using hGrank
  have hRestrictCard :
      (M.restrict (H ∩ K)).E.encard = ((2 * k : ℕ) : ℕ∞) := by
    rw [Matroid.restrict_ground_eq, ← hGfin.cast_ncard_eq, hGcard]
  exact exists_cyclicBasisOrder_of_rank_two
    (M.restrict (H ∩ K)) k (by omega)
    hRestrictFinite hRestrictRank hRestrictCard
    (dangerous_inter_restrict_uniformlyDense
      hk hE hRank hEcard hStrict hH hK hne)

/-- Conditional formal version of the rank-three input in the `t=1`
construction.  The HigherRankKUM repository formalizes the divisible rank-three
theorem internally; the known coprime theorem is represented here by a full
rank-three solver hypothesis. -/
theorem exists_hyperplane_cbo_of_one_dangerous
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hSolve3 : SolvesKUMAtRank α 3)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H) :
    ∃ order : Fin (3 * k + 1) ≃ (M.restrict H).E,
      CyclicBasisOrder (M.restrict H) 3 (by omega) order := by
  have hHfin : H.Finite := hH.finite hE
  have hRestrictFinite : (M.restrict H).E.Finite := by
    simpa using hHfin
  have hRestrictRank : (M.restrict H).eRank = (3 : ℕ∞) := by
    simpa using hH.2.1
  have hRestrictCard :
      (M.restrict H).E.encard = ((3 * k + 1 : ℕ) : ℕ∞) := by
    simpa using hH.2.2
  exact hSolve3 (3 * k + 1) (M.restrict H)
    (by omega) (by omega) hRestrictFinite hRestrictRank hRestrictCard
    (dangerous_restrict_uniformlyDenseRatio hE hRank hStrict hH)

end

end Rank4DangerousBranches
end HigherRankKUM
