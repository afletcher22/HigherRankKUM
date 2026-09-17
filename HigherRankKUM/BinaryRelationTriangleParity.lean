import HigherRankKUM.BinaryRelationParity

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- For four forced Boolean transitions, cyclic satisfiability is equivalent
to the two adjacent relation-pairs having the same parity. -/
private theorem cyclicSatisfiable_four_iff_pair_parities
    {A B C D : Relation}
    (hA : BijectionRelation A) (hB : BijectionRelation B)
    (hC : BijectionRelation C) (hD : BijectionRelation D) :
    CyclicSatisfiable [A, B, C, D] ↔
      (CyclicSatisfiable [A, B] ↔ CyclicSatisfiable [C, D]) := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hA with h | h <;> subst A <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hB with h | h <;> subst B <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hC with h | h <;> subst C <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hD with h | h <;> subst D
  all_goals simp [CyclicSatisfiable, composeList, comp, idRel, flipRel]

/-- Two odd triangles sharing their middle relation identify the parities of
the opposite relation-pairs.  This is the left-hand cancellation shape used
by the wholesale-swap argument. -/
private theorem pair_parity_iff_of_shared_middle_triangle_obstructions
    {A B C D U : Relation}
    (hA : BijectionRelation A) (hB : BijectionRelation B)
    (hC : BijectionRelation C) (hD : BijectionRelation D)
    (hU : BijectionRelation U)
    (h₁ : ¬ CyclicSatisfiable [A, U, C])
    (h₂ : ¬ CyclicSatisfiable [D, U, B]) :
    CyclicSatisfiable [A, B] ↔ CyclicSatisfiable [C, D] := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hA with h | h <;> subst A <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hB with h | h <;> subst B <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hC with h | h <;> subst C <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hD with h | h <;> subst D <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hU with h | h <;> subst U
  all_goals
    simp [CyclicSatisfiable, composeList, comp, idRel, flipRel] at h₁ h₂ ⊢

/-- Mirror cancellation shape in which the shared transition appears first in
both odd triangles. -/
private theorem pair_parity_iff_of_shared_left_triangle_obstructions
    {A B C D U : Relation}
    (hA : BijectionRelation A) (hB : BijectionRelation B)
    (hC : BijectionRelation C) (hD : BijectionRelation D)
    (hU : BijectionRelation U)
    (h₁ : ¬ CyclicSatisfiable [U, C, A])
    (h₂ : ¬ CyclicSatisfiable [U, B, D]) :
    CyclicSatisfiable [A, B] ↔ CyclicSatisfiable [C, D] := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hA with h | h <;> subst A <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hB with h | h <;> subst B <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hC with h | h <;> subst C <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hD with h | h <;> subst D <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hU with h | h <;> subst U
  all_goals
    simp [CyclicSatisfiable, composeList, comp, idRel, flipRel] at h₁ h₂ ⊢

/-- Pure Boolean bookkeeping behind the wholesale-swap parity argument.

Suppose four old forced relations `R₁,...,R₄` and four new forced relations
`S₁,...,S₄` are linked by four odd triangles in the geometric order that
arises from a wholesale swap.  The two left triangles share an auxiliary
forced relation `U`, and the two right triangles share an auxiliary forced
relation `V`:

`[R₁,U,S₁]`, `[S₂,U,R₂]`, `[V,S₃,R₃]`, `[V,R₄,S₄]`.

Then the old four-cycle has a fixed point exactly when the new four-cycle
does. XORing the two left triangle parities cancels `U`; XORing the two
right parities cancels `V`. -/
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
  have hLeft : CyclicSatisfiable [R₁, R₂] ↔ CyclicSatisfiable [S₁, S₂] :=
    pair_parity_iff_of_shared_middle_triangle_obstructions
      hR₁ hR₂ hS₁ hS₂ hU hL₁ hL₂
  have hRight : CyclicSatisfiable [R₃, R₄] ↔ CyclicSatisfiable [S₃, S₄] :=
    pair_parity_iff_of_shared_left_triangle_obstructions
      hR₃ hR₄ hS₃ hS₄ hV hR₁' hR₂'
  rw [cyclicSatisfiable_four_iff_pair_parities hR₁ hR₂ hR₃ hR₄,
    cyclicSatisfiable_four_iff_pair_parities hS₁ hS₂ hS₃ hS₄,
    hLeft, hRight]

end BinaryRelationCycle
end HigherRankKUM
