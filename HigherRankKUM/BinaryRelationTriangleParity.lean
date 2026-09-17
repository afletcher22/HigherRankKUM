import HigherRankKUM.BinaryRelationParity

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- Pure Boolean bookkeeping behind the wholesale-swap parity argument.

Suppose four old forced relations `R₁,...,R₄` and four new forced relations
`S₁,...,S₄` are linked by four odd triangles in the geometric order that
arises from a wholesale swap.  The two left triangles share an auxiliary
forced relation `U`, and the two right triangles share an auxiliary forced
relation `V`:

`[R₁,U,S₁]`, `[S₂,U,R₂]`, `[V,S₃,R₃]`, `[V,R₄,S₄]`.

Then the old four-cycle has a fixed point exactly when the new four-cycle
does.  For identity/flip permutations, an unsatisfiable triangle has odd flip
parity. XORing the two left triangle equations cancels `U`; XORing the two
right equations cancels `V`.  The total old and new four-cycle parities are
therefore equal. -/
theorem cyclicSatisfiable_four_iff_of_shared_triangle_obstructions
    {R₁ R₂ R₃ R₄ S₁ S₂ S₃ S₄ U V : Relation}
    (hR₁ : BijectionRelation R₁) (hR₂ : BijectionRelation R₂)
    (hR₃ : BijectionRelation R₃) (hR₄ : BijectionRelation R₄)
    (hS₁ : BijectionRelation S₁) (hS₂ : BijectionRelation S₂)
    (hS₃ : BijectionRelation S₃) (hS₄ : BijectionRelation S₄)
    (hU : BijectionRelation U) (hV : BijectionRelation V)
    (hL₁ : ¬ CyclicSatisfiable [R₁, U, S₁])
    (hL₂ : ¬ CyclicSatisfiable [S₂, U, R₂])
    (hR₁' : ¬ CyclicSatisfiable [V, S₃, R₃])
    (hR₂' : ¬ CyclicSatisfiable [V, R₄, S₄]) :
    CyclicSatisfiable [R₁, R₂, R₃, R₄] ↔
      CyclicSatisfiable [S₁, S₂, S₃, S₄] := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR₁ with h | h <;> subst R₁ <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hR₂ with h | h <;> subst R₂ <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hR₃ with h | h <;> subst R₃ <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hR₄ with h | h <;> subst R₄ <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hS₁ with h | h <;> subst S₁ <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hS₂ with h | h <;> subst S₂ <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hS₃ with h | h <;> subst S₃ <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hS₄ with h | h <;> subst S₄ <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hU with h | h <;> subst U <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hV with h | h <;> subst V <;>
  all_goals
    simp [CyclicSatisfiable, composeList, comp, idRel, flipRel,
      idRel_ne_flipRel, flipRel_ne_idRel] at hL₁ hL₂ hR₁' hR₂' ⊢

end BinaryRelationCycle
end HigherRankKUM
