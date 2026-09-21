import HigherRankKUM.LowRank.RankTwo
import HigherRankKUM.RationalDensity
import Mathlib.Combinatorics.Matroid.Dual

namespace HigherRankKUM
namespace Rank4

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- On six elements, rank four and rank two are complementary under duality.
Uniform density at ratio 6/4 therefore turns into integer uniform density
with density three in the dual. -/
theorem dual_uniformlyDense_three_of_rank_four_six
    (M : Matroid α)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = (6 : ℕ∞))
    (hDense : UniformlyDenseRatio M 6 4) :
    UniformlyDense M✶ 3 := by
  intro X hX
  have hXE : X ⊆ M.E := by simpa using hX
  have hXfin : X.Finite := hE.subset hXE
  have hCfin : (M.E \ X).Finite := hE.sdiff
  have hCsub : M.E \ X ⊆ M.E := Set.sdiff_subset
  have hd := hDense (M.E \ X) hCsub
  have hdual := M.eRk_dual_add_eRank X hXE
  have hEn : M.E.ncard = 6 := by
    rw [← hE.cast_ncard_eq] at hEcard
    exact_mod_cast hEcard
  have hXle : X.ncard ≤ 6 := by
    rw [← hEn]
    exact Set.ncard_le_ncard hXE hE
  have hCcard : (M.E \ X).ncard = 6 - X.ncard := by
    rw [Set.ncard_sdiff hXE hXfin, hEn]
  have hCrkBound : M.eRk (M.E \ X) ≤ (4 : ℕ∞) := by
    rw [← hRank]
    exact M.eRk_le_eRank _
  obtain ⟨c, hCrk, _⟩ := ENat.le_natCast_iff.mp hCrkBound
  have hDrkBound : M✶.eRk X ≤ (2 : ℕ∞) := by
    have hranks := M.eRank_add_eRank_dual
    rw [hRank, hEcard] at hranks
    have hDualRank : M✶.eRank = (2 : ℕ∞) := by
      have hranks' : (4 : ℕ∞) + M✶.eRank = 4 + (2 : ℕ∞) := by
        calc
          (4 : ℕ∞) + M✶.eRank = 6 := hranks
          _ = 4 + (2 : ℕ∞) := by norm_num
      exact ENat.add_right_injective_of_ne_top (n := (4 : ℕ∞)) (by simp) hranks'
    rw [← hDualRank]
    exact M✶.eRk_le_eRank X
  obtain ⟨d, hDrk, _⟩ := ENat.le_natCast_iff.mp hDrkBound
  have hdNat' : 4 * (M.E \ X).ncard ≤ 6 * c := by
    rw [← hCfin.cast_ncard_eq, hCrk] at hd
    exact_mod_cast hd
  have hdNat : 4 * (6 - X.ncard) ≤ 6 * c := by
    simpa [hCcard] using hdNat'
  have hdualNat : d + 4 = c + X.ncard := by
    rw [hDrk, hRank, hCrk, ← hXfin.cast_ncard_eq] at hdual
    exact_mod_cast hdual
  have hgoal : X.ncard ≤ 3 * d := by omega
  rw [← hXfin.cast_ncard_eq, hDrk]
  exact_mod_cast hgoal

/-- The six-element boundary of rank-four KUM.

A uniformly dense rank-four matroid on six elements has rank-two dual of
integer density three.  The internal rank-two theorem gives a cyclic basis
order of the dual; complements of its adjacent dual bases are precisely the
four-windows in the same six-cycle, hence bases of the original matroid. -/
theorem exists_cyclicBasisOrder_of_rank_four_six
    (M : Matroid α)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = (6 : ℕ∞))
    (hDense : UniformlyDenseRatio M 6 4) :
    ∃ order : Fin 6 ≃ M.E,
      CyclicBasisOrder M 4 (by omega) order := by
  have hDualDense : UniformlyDense M✶ 3 :=
    dual_uniformlyDense_three_of_rank_four_six M hE hRank hEcard hDense
  have hDualRank : M✶.eRank = (2 : ℕ∞) := by
    have hranks := M.eRank_add_eRank_dual
    rw [hRank, hEcard] at hranks
    have hranks' : (4 : ℕ∞) + M✶.eRank = 4 + (2 : ℕ∞) := by
      calc
        (4 : ℕ∞) + M✶.eRank = 6 := hranks
        _ = 4 + (2 : ℕ∞) := by norm_num
    exact ENat.add_right_injective_of_ne_top (n := (4 : ℕ∞)) (by simp) hranks'
  have hDualE : M✶.E.Finite := by simpa using hE
  have hDualCard : M✶.E.encard = ((2 * 3 : ℕ) : ℕ∞) := by
    simpa using hEcard
  obtain ⟨σ, hσ⟩ :=
    exists_cyclicBasisOrder_of_rank_two M✶ 3 (by omega)
      hDualE hDualRank hDualCard hDualDense
  refine ⟨σ, ?_⟩
  simpa using
    (cyclicBasisOrder_of_dual M (n := 6) (r := 4) (s := 2)
      (by omega) (by omega) σ hσ)

end
end Rank4
end HigherRankKUM
