import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4AdjacentSwapObstruction

open Set
open scoped Matroid

variable {α : Type*}

/-- If insert a I is a base, and an outside ground element b cannot
replace a while keeping a base, then b is spanned by the unchanged
interior I.

This is the elementary closure obstruction behind a failed adjacent swap in a
cyclic basis ordering. -/
theorem mem_closure_of_replacement_not_isBase
    {M : Matroid α} {I : Set α} {a b : α}
    (hB : M.IsBase (insert a I))
    (haI : a ∉ I)
    (hbB : b ∉ insert a I)
    (hbE : b ∈ M.E)
    (hnot : ¬ M.IsBase (insert b I)) :
    b ∈ M.closure I := by
  have hI : M.Indep I :=
    hB.indep.subset (Set.subset_insert a I)
  have hbI : b ∉ I := by
    intro hb
    exact hbB (Set.mem_insert_iff.2 (Or.inr hb))
  by_contra hbcl
  have hbi : M.Indep (insert b I) := by
    rw [hI.insert_indep_iff_of_notMem hbI]
    exact ⟨hbE, hbcl⟩
  have hrep :
      M.Indep (insert b ((insert a I) \ {a})) := by
    simpa [haI] using hbi
  have hnew :=
    hB.exchange_isBase_of_indep (e := a) (f := b) hbB hrep
  apply hnot
  simpa [haI] using hnew

/-- Two-sided form for an adjacent transposition.

Suppose the old left boundary window is insert a L and the old right
boundary window is insert b R, both bases. Assume a,b are genuinely the
two boundary entries, so each is outside the other old boundary window. If
after swapping them the two replacement windows cannot both be bases, then
either b is in the closure of the left unchanged triple/core, or a is in
the closure of the right unchanged triple/core. -/
theorem closure_obstruction_of_failed_adjacent_swap
    {M : Matroid α} {L R : Set α} {a b : α}
    (hLeft : M.IsBase (insert a L))
    (hRight : M.IsBase (insert b R))
    (haL : a ∉ L)
    (hbLeft : b ∉ insert a L)
    (hbR : b ∉ R)
    (haRight : a ∉ insert b R)
    (hfail :
      ¬ (M.IsBase (insert b L) ∧ M.IsBase (insert a R))) :
    b ∈ M.closure L ∨ a ∈ M.closure R := by
  by_cases hLb : M.IsBase (insert b L)
  · right
    have hnotR : ¬ M.IsBase (insert a R) := by
      intro hRa
      exact hfail ⟨hLb, hRa⟩
    have haE : a ∈ M.E :=
      hLeft.subset_ground (Set.mem_insert a L)
    exact mem_closure_of_replacement_not_isBase
      hRight hbR haRight haE hnotR
  · left
    have hbE : b ∈ M.E :=
      hRight.subset_ground (Set.mem_insert b R)
    exact mem_closure_of_replacement_not_isBase
      hLeft haL hbLeft hbE hLb

end Rank4AdjacentSwapObstruction
end HigherRankKUM
