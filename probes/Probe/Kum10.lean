import Probe.EncFBridge
import Probe.Kum10BaseG2
import Probe.Kum10BaseG3
import Probe.Kum10BaseG4
import Probe.Kum10BaseL4
import Probe.Kum10Light
import HigherRankKUM.Rank4.Unconditional

/-!
# Rank-4 KUM on 10 elements

Let `M` be a uniformly dense rank-4 matroid on 10 elements.

* If `M` has a nonempty proper tight set, or a dangerous plane (7 elements), the Lean reductions
  of the main library give a cyclic basis ordering.
* Otherwise `M` is strict with `t = 0`: points have at most 2 elements, lines 4, planes 6.
  * With a 6-element plane `K`, the base lemma of Theorem G applies, with one certificate for
    each value 2, 3, 4 of `r(E - K)`.
  * With a 4-element line, the base lemma of Theorem L4 applies.
  * Otherwise the light certificate applies.
-/

namespace HigherRankKUM

open Set Probe.Enc
open scoped Matroid

/-- **Rank-4 KUM on 10 elements.** -/
theorem solvesKUMAtRankSize_four_ten {α : Type*} : SolvesKUMAtRankSize α 4 10 := by
  intro M hr hn hE hRank hEcard hDense
  have hRank4 : M.eRank = 4 := by simpa using hRank
  have hEcard' : M.E.encard = ((4 * 2 + 2 : ℕ) : ℕ∞) := hEcard.trans (by norm_num)
  -- a nonempty proper tight set
  by_cases htight : ∃ X, TightRatio M 10 4 X ∧ X.Nonempty ∧ X ≠ M.E
  · obtain ⟨X, hX, hne, hprop⟩ := htight
    exact exists_cyclicBasisOrder_congr M (by norm_num) rfl
      (exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight' M 2 hE hRank4
        hEcard' hDense hX hne hprop)
  -- otherwise `M` is strict
  have hStrict : StrictlyUniformlyDenseRatio M 10 4 := by
    intro X hX hne hprop
    exact lt_of_le_of_ne (hDense X hX) fun heq => htight ⟨X, ⟨hX, heq⟩, hne, hprop⟩
  -- a dangerous plane
  by_cases hdanger : ∃ H, Rank4GcdTwoDeletion.DangerousHyperplane M 2 H
  · obtain ⟨H, hH⟩ := hdanger
    exact exists_cyclicBasisOrder_congr M (by norm_num) rfl
      (Rank4DangerousBranches.exists_cbo_of_dangerous_hyperplane' (le_refl 2) hE hRank4 hEcard'
        hStrict hH)
  have hT : Hitting.StrictT0 M 2 :=
    ⟨hE, hRank4, hEcard', hStrict, fun H hH => hdanger ⟨H, hH⟩⟩
  -- a 6-element plane: the base lemma of Theorem G
  by_cases h6 : ∃ K, M.IsFlat K ∧ M.eRk K = 3 ∧ K.encard = ((3 * 2 : ℕ) : ℕ∞)
  · obtain ⟨K, hKflat, hKrank, hKcard⟩ := h6
    have hKcard' : K.encard = ((6 : ℕ) : ℕ∞) := hKcard
    have hEcard6 : M.E.encard = ((6 + 4 : ℕ) : ℕ∞) := hEcard.trans (by norm_num)
    obtain ⟨c, hc, hc4⟩ := hT.exists_eRk_eq (M.E \ K)
    have hc2 : 2 ≤ c := by
      have h := hDense (M.E \ K) diff_subset
      rw [encard_diff_eq hE hKflat.subset_ground hEcard6 hKcard', hc] at h
      have h' : 4 * 4 ≤ 10 * c := by exact_mod_cast h
      omega
    interval_cases c
    · exact cbo_of_basePlane BaseG2.no_model hE hRank4 hEcard6 hDense hKflat hKrank hKcard' hc
    · exact cbo_of_basePlane BaseG3.no_model hE hRank4 hEcard6 hDense hKflat hKrank hKcard' hc
    · exact cbo_of_basePlane BaseG4.no_model hE hRank4 hEcard6 hDense hKflat hKrank hKcard' hc
  -- a 4-element line: the base lemma of Theorem L4
  by_cases h4 : ∃ L, M.IsFlat L ∧ M.eRk L = 2 ∧ L.encard = ((2 * 2 : ℕ) : ℕ∞)
  · obtain ⟨L, hLflat, hLrank, hLcard⟩ := h4
    exact cbo_of_baseLine BaseL4.no_model hE hRank4 (hEcard.trans (by norm_num)) hDense hLflat
      hLrank hLcard
  -- neither
  push_neg at h6 h4
  exact cbo_of_light Light.no_model hT h6 h4

#print axioms solvesKUMAtRankSize_four_ten

end HigherRankKUM
