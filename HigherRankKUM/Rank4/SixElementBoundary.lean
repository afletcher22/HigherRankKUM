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
      apply ENat.add_right_injective_of_ne_top (by simp)
    simpa using hranks
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

/-- Four cyclic positions on six elements, expanded as an explicit set. -/
theorem cyclicWindow_four_six_eq
    (M : Matroid α) (σ : Fin 6 ≃ M.E) (i : Fin 6) :
    cyclicWindow 4 (by omega) σ i =
      ({(σ i : α),
        (σ (cyclicIndex 6 (by omega) i 1) : α),
        (σ (cyclicIndex 6 (by omega) i 2) : α),
        (σ (cyclicIndex 6 (by omega) i 3) : α)} : Set α) := by
  ext x
  simp only [cyclicWindow, Set.mem_range,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [cyclicIndex_zero]
  · rintro (hx | hx | hx | hx)
    · subst x; exact ⟨0, by simp [cyclicIndex_zero]⟩
    · subst x; exact ⟨1, rfl⟩
    · subst x; exact ⟨2, rfl⟩
    · subst x; exact ⟨3, rfl⟩

/-- On a six-cycle, the complement of the two positions starting four steps
after `i` is exactly the four-position window starting at `i`. -/
theorem sdiff_two_window_eq_four_window
    (M : Matroid α) (σ : Fin 6 ≃ M.E) (i : Fin 6) :
    M.E \ cyclicWindow 2 (by omega) σ
        (cyclicIndex 6 (by omega) i 4) =
      cyclicWindow 4 (by omega) σ i := by
  rw [cyclicWindow_two_eq_pair, cyclicWindow_four_six_eq M]
  classical
  fin_cases i <;> ext x <;>
    simp only [cyclicIndex, Set.mem_diff, Set.mem_insert_iff,
      Set.mem_singleton_iff] <;>
    constructor
  all_goals
    intro h
    try
      rcases h with ⟨hxE, hne⟩
      let q : Fin 6 := σ.symm ⟨x, hxE⟩
      have hqx : (σ q : α) = x := by
        simpa [q] using congrArg Subtype.val (σ.apply_symm_apply ⟨x, hxE⟩)
      fin_cases q <;> simp [cyclicIndex] at hqx hne ⊢ <;> simp_all
    try
      rcases h with (rfl | rfl | rfl | rfl) <;>
        constructor <;> simp [cyclicIndex]

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
    apply ENat.add_right_injective_of_ne_top (by simp)
    simpa using hranks
  have hDualE : M✶.E.Finite := by simpa using hE
  have hDualCard : M✶.E.encard = ((2 * 3 : ℕ) : ℕ∞) := by
    simpa using hEcard
  obtain ⟨σ, hσ⟩ :=
    exists_cyclicBasisOrder_of_rank_two M✶ 3 (by omega)
      hDualE hDualRank hDualCard hDualDense
  refine ⟨σ, ?_⟩
  intro i
  let j : Fin 6 := cyclicIndex 6 (by omega) i 4
  have hj : M✶.IsBase (cyclicWindow 2 (by omega) σ j) := hσ j
  have hc : M.IsBase (M.E \ cyclicWindow 2 (by omega) σ j) := by
    simpa using hj.compl_isBase_of_dual
  simpa [j, sdiff_two_window_eq_four_window M σ i] using hc

end
end Rank4
end HigherRankKUM
