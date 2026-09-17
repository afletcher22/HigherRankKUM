import Mathlib.Combinatorics.Matroid.Minor.Restrict
import Mathlib.Combinatorics.Matroid.Dual
import Mathlib.Combinatorics.Matroid.Closure

namespace HigherRankKUM
namespace Rank4ThreePairDual

open Set

variable {α : Type*}

/-- Set-theoretic core of the six-element duality argument.

If `X,Y,Z` are pairwise disjoint on the `X` side, the union `X ∪ Y ∪ Z`
is spanning, and `Y ∪ Z` is a base of `M`, then `X` is a base in the dual
of the restriction to the union.  This is simply base-complement duality,
but packaging it here avoids repeating complement algebra in each cyclic
permutation of the three pair blocks. -/
theorem dual_restrict_pair_isBase
    (M : Matroid α) {X Y Z : Set α}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hspan : M.Spanning (X ∪ Y ∪ Z))
    (hYZbase : M.IsBase (Y ∪ Z)) :
    ((M ↾ (X ∪ Y ∪ Z))✶).IsBase X := by
  let U : Set α := X ∪ Y ∪ Z
  let R : Matroid α := M ↾ U
  have hYZsub : Y ∪ Z ⊆ U := by
    intro e he
    rcases he with heY | heZ
    · exact Or.inl (Or.inr heY)
    · exact Or.inr heZ
  have hRbase : R.IsBase (Y ∪ Z) := by
    change (M ↾ U).IsBase (Y ∪ Z)
    exact (hspan.isBase_restrict_iff).2 ⟨hYZbase, hYZsub⟩
  have hcomp : R.E \ (Y ∪ Z) = X := by
    change U \ (Y ∪ Z) = X
    ext e
    constructor
    · rintro ⟨heU, hnot⟩
      rcases heU with heXY | heZ
      · rcases heXY with heX | heY
        · exact heX
        · exact (hnot (Or.inl heY)).elim
      · exact (hnot (Or.inr heZ)).elim
    · intro heX
      refine ⟨Or.inl (Or.inl heX), ?_⟩
      intro heYZ
      rcases heYZ with heY | heZ
      · exact Set.disjoint_left.1 hXY heX heY
      · exact Set.disjoint_left.1 hXZ heX heZ
  have hdual := (R.base_iff_dual_isBase_compl hRbase.subset_ground).1 hRbase
  simpa [hcomp] using hdual

end Rank4ThreePairDual
end HigherRankKUM
