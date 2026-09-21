import HigherRankKUM.CyclicIndex
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4CycleThreeGood

noncomputable section

/-- On a cycle of length 3k with no three consecutive bad positions, either
there is a pair of good positions at distance one or two, or the good pattern
is forced to propagate with period three.

This is the exact extremal distinction between the saturated 3k core and the
earlier dangerous-hyperplane 3k+1 core: the periodic GBBGBB... word is now
possible. -/
theorem exists_near_good_or_period_three
    {k : ℕ} (hk : 0 < k)
    (Good : Fin (3 * k) → Prop)
    (hNoThreeBad :
      ∀ i : Fin (3 * k),
        Good i ∨
        Good (cyclicIndex (3 * k) (by omega) i 1) ∨
        Good (cyclicIndex (3 * k) (by omega) i 2)) :
    (∃ i : Fin (3 * k),
      (Good i ∧
        Good (cyclicIndex (3 * k) (by omega) i 1)) ∨
      (Good i ∧
        Good (cyclicIndex (3 * k) (by omega) i 2))) ∨
    ∃ s : Fin (3 * k),
      Good s ∧
      ∀ i : Fin (3 * k), Good i →
        ¬ Good (cyclicIndex (3 * k) (by omega) i 1) ∧
        ¬ Good (cyclicIndex (3 * k) (by omega) i 2) ∧
        Good (cyclicIndex (3 * k) (by omega) i 3) := by
  by_cases hnear :
      ∃ i : Fin (3 * k),
        (Good i ∧
          Good (cyclicIndex (3 * k) (by omega) i 1)) ∨
        (Good i ∧
          Good (cyclicIndex (3 * k) (by omega) i 2))
  · exact Or.inl hnear
  · right
    push_neg at hnear
    have hNoOne :
        ∀ i : Fin (3 * k), Good i →
          ¬ Good (cyclicIndex (3 * k) (by omega) i 1) := by
      intro i hi h1
      exact (hnear i).1 hi h1
    have hNoTwo :
        ∀ i : Fin (3 * k), Good i →
          ¬ Good (cyclicIndex (3 * k) (by omega) i 2) := by
      intro i hi h2
      exact (hnear i).2 hi h2
    let z : Fin (3 * k) := ⟨0, by omega⟩
    have hz := hNoThreeBad z
    obtain ⟨s, hs⟩ :
        ∃ s : Fin (3 * k), Good s := by
      rcases hz with hz0 | hz1 | hz2
      · exact ⟨z, hz0⟩
      · exact
          ⟨cyclicIndex (3 * k) (by omega) z 1, hz1⟩
      · exact
          ⟨cyclicIndex (3 * k) (by omega) z 2, hz2⟩
    refine ⟨s, hs, ?_⟩
    intro i hi
    have h1 := hNoOne i hi
    have h2 := hNoTwo i hi
    refine ⟨h1, h2, ?_⟩
    have htri :=
      hNoThreeBad
        (cyclicIndex (3 * k) (by omega) i 1)
    rcases htri with hg1 | hg2 | hg3
    · exact (h1 hg1).elim
    · have hEq :
          cyclicIndex (3 * k) (by omega)
              (cyclicIndex (3 * k) (by omega) i 1) 1 =
            cyclicIndex (3 * k) (by omega) i 2 := by
        rw [cyclicIndex_add]
      exact (h2 (by simpa [hEq] using hg2)).elim
    · have hEq :
          cyclicIndex (3 * k) (by omega)
              (cyclicIndex (3 * k) (by omega) i 1) 2 =
            cyclicIndex (3 * k) (by omega) i 3 := by
        rw [cyclicIndex_add]
      simpa [hEq] using hg3

/-- In the periodic alternative, every good position has two bad successors
and a good third successor. -/
theorem period_three_of_no_near_good
    {k : ℕ} (hk : 0 < k)
    (Good : Fin (3 * k) → Prop)
    (hNoThreeBad :
      ∀ i : Fin (3 * k),
        Good i ∨
        Good (cyclicIndex (3 * k) (by omega) i 1) ∨
        Good (cyclicIndex (3 * k) (by omega) i 2))
    (hNoNear :
      ∀ i : Fin (3 * k),
        ¬ (Good i ∧
          Good (cyclicIndex (3 * k) (by omega) i 1)) ∧
        ¬ (Good i ∧
          Good (cyclicIndex (3 * k) (by omega) i 2))) :
    ∃ s : Fin (3 * k),
      Good s ∧
      ∀ i : Fin (3 * k), Good i →
        ¬ Good (cyclicIndex (3 * k) (by omega) i 1) ∧
        ¬ Good (cyclicIndex (3 * k) (by omega) i 2) ∧
        Good (cyclicIndex (3 * k) (by omega) i 3) := by
  rcases exists_near_good_or_period_three hk Good hNoThreeBad with hnear | hper
  · rcases hnear with ⟨i, h1 | h2⟩
    · exact (hNoNear i).1 h1 |>.elim
    · exact (hNoNear i).2 h2 |>.elim
  · exact hper

end

end Rank4CycleThreeGood
end HigherRankKUM
