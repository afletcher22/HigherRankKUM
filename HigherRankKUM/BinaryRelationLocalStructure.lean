import HigherRankKUM.BinaryRelationCycle

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- Three distinct allowed Boolean combinations.  On a 2-by-2 relation this
is equivalent to allowing at least three of the four possible pairs. -/
def HasThreeAllowed (R : Relation) : Prop :=
  ∃ p q r : Bool × Bool,
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    R p.1 p.2 ∧ R q.1 q.2 ∧ R r.1 r.2

/-- A full-support Boolean relation is either functional (hence a bijection)
or allows at least three combinations. -/
theorem hasThreeAllowed_of_fullSupport_of_not_functional
    {R : Relation} (hfull : FullSupport R) (hnf : ¬ Functional R) :
    HasThreeAllowed R := by
  obtain ⟨x, hx0, hx1⟩ := exists_both_of_not_functional hnf
  cases x
  · obtain ⟨y, hy⟩ := hfull.1 true
    refine ⟨(false, false), (false, true), (true, y), ?_⟩
    simp [hx0, hx1, hy]
  · obtain ⟨y, hy⟩ := hfull.1 false
    refine ⟨(true, false), (true, true), (false, y), ?_⟩
    simp [hx0, hx1, hy]

/-- Therefore, if a full-support local relation does not allow three distinct
combinations, its exactly-two-or-fewer pattern is forced to be a bijection.
Full support itself supplies at least two combinations, so this is the formal
version of “exactly two implies a bijection”. -/
theorem bijectionRelation_of_not_hasThreeAllowed
    {R : Relation} (hfull : FullSupport R) (hsmall : ¬ HasThreeAllowed R) :
    BijectionRelation R := by
  refine ⟨hfull, ?_⟩
  by_contra hnf
  exact hsmall (hasThreeAllowed_of_fullSupport_of_not_functional hfull hnf)

/-- Two pointwise-disjoint full-support Boolean relations are necessarily
bijection relations.  Indeed, if one relation branched in some row, the other
relation's row support would force an overlap in that same row.

On a `2 × 2` grid this is the abstract reason that the exceptional no-cross
local repair geometry consists of complementary perfect matchings rather than
larger cross-base patterns. -/
theorem bijectionRelations_of_disjoint_fullSupport
    {R S : Relation}
    (hR : FullSupport R) (hS : FullSupport S)
    (hdisj : ∀ x y, ¬ (R x y ∧ S x y)) :
    BijectionRelation R ∧ BijectionRelation S := by
  have hRfun : Functional R := by
    by_contra hnf
    obtain ⟨x, hx0, hx1⟩ := exists_both_of_not_functional hnf
    obtain ⟨y, hy⟩ := hS.1 x
    cases y
    · exact hdisj x false ⟨hx0, hy⟩
    · exact hdisj x true ⟨hx1, hy⟩
  have hSfun : Functional S := by
    by_contra hnf
    obtain ⟨x, hx0, hx1⟩ := exists_both_of_not_functional hnf
    obtain ⟨y, hy⟩ := hR.1 x
    cases y
    · exact hdisj x false ⟨hy, hx0⟩
    · exact hdisj x true ⟨hy, hx1⟩
  exact ⟨⟨hR, hRfun⟩, ⟨hS, hSfun⟩⟩

end BinaryRelationCycle
end HigherRankKUM
