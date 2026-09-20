import HigherRankKUM.BinaryRelationCycle

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- Functional relations compose. -/
theorem functional_comp {R S : Relation}
    (hR : Functional R) (hS : Functional S) : Functional (comp R S) := by
  intro x z₁ z₂ hxz₁ hxz₂
  obtain ⟨y₁, hxy₁, hy₁z₁⟩ := hxz₁
  obtain ⟨y₂, hxy₂, hy₂z₂⟩ := hxz₂
  have hy : y₁ = y₂ := hR hxy₁ hxy₂
  subst y₂
  exact hS hy₁z₁ hy₂z₂

/-- A list of forced local transitions has a forced total transition. -/
theorem composeList_functional
    {Rs : List Relation} (h : ∀ R ∈ Rs, Functional R) :
    Functional (composeList Rs) := by
  induction Rs with
  | nil =>
      intro x y z hxy hxz
      simpa [composeList, idRel] using hxy.symm.trans hxz
  | cons R Rs ih =>
      exact functional_comp (h R (by simp))
        (ih (fun S hS => h S (by simp [hS])))

/-- On two states, a full-support forced transition with no fixed point is
exactly the flip: false goes to true and true goes to false. -/
theorem forced_flip_of_no_fixed_point
    {R : Relation} (hfull : FullSupport R) (hfun : Functional R)
    (hnofix : ¬ ∃ x, R x x) :
    R false true ∧ R true false := by
  constructor
  · obtain ⟨y, hy⟩ := hfull.1 false
    cases y
    · exact False.elim (hnofix ⟨false, hy⟩)
    · exact hy
  · obtain ⟨y, hy⟩ := hfull.1 true
    cases y
    · exact hy
    · exact False.elim (hnofix ⟨true, hy⟩)

/-- Thus if all local relations are bijections and the total composition is
fixed-point-free, the total transition is literally the Boolean flip. -/
theorem composeList_is_flip_of_forced_no_fixed
    {Rs : List Relation}
    (hbij : ∀ R ∈ Rs, BijectionRelation R)
    (hnofix : ¬ ∃ x, composeList Rs x x) :
    composeList Rs false true ∧ composeList Rs true false := by
  apply forced_flip_of_no_fixed_point
  · exact composeList_fullSupport (fun R hR => (hbij R hR).1)
  · exact composeList_functional (fun R hR => (hbij R hR).2)
  · exact hnofix

end BinaryRelationCycle
end HigherRankKUM
