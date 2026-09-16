import HigherRankKUM.BinaryRelationCycle

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- The unique fixed-point-free bijection relation on `Bool`. -/
def flipRel : Relation := fun x y => x ≠ y

/-- Relabel the input side of a Boolean relation by swapping its two labels
when `b = true`. -/
def relabelInput (b : Bool) (R : Relation) : Relation :=
  if b then fun x y => R (Bool.not x) y else R

/-- Relabel the output side of a Boolean relation by swapping its two labels
when `b = true`. -/
def relabelOutput (b : Bool) (R : Relation) : Relation :=
  if b then fun x y => R x (Bool.not y) else R

/-- Every full-support functional relation on two states is one of the two
Boolean permutations: the identity or the flip. -/
theorem eq_idRel_or_eq_flipRel_of_bijection
    {R : Relation} (hR : BijectionRelation R) :
    R = idRel ∨ R = flipRel := by
  obtain ⟨y, hy⟩ := hR.1.1 false
  cases y with
  | false =>
      left
      have hn01 : ¬ R false true := by
        intro h01
        exact Bool.false_ne_true (hR.2 hy h01)
      obtain ⟨x, hx1⟩ := hR.1.2 true
      have h11 : R true true := by
        cases x with
        | false => exact (hn01 hx1).elim
        | true => exact hx1
      have hn10 : ¬ R true false := by
        intro h10
        exact Bool.false_ne_true (hR.2 h10 h11)
      funext x z
      apply propext
      cases x <;> cases z <;> simp [idRel, hy, hn01, h11, hn10]
  | true =>
      right
      have hn00 : ¬ R false false := by
        intro h00
        exact Bool.false_ne_true (hR.2 h00 hy)
      obtain ⟨x, hx0⟩ := hR.1.2 false
      have h10 : R true false := by
        cases x with
        | false => exact (hn00 hx0).elim
        | true => exact hx0
      have hn11 : ¬ R true true := by
        intro h11
        exact Bool.false_ne_true (hR.2 h10 h11)
      funext x z
      apply propext
      cases x <;> cases z <;> simp [flipRel, hy, hn00, h10, hn11]

/-- Paired input/output relabellings do not change the cyclic parity of four
forced Boolean relations.  The same two label swaps occur twice, so the total
composition is identity exactly when it was identity before the relabelling.

This is the abstract parity algebra needed by the six-block repair argument;
the matroid layer only has to identify which of the four affected local
relations receives each relabelling. -/
theorem cyclicSatisfiable_four_relabel
    {R₁ R₂ R₃ R₄ : Relation}
    (h₁ : BijectionRelation R₁) (h₂ : BijectionRelation R₂)
    (h₃ : BijectionRelation R₃) (h₄ : BijectionRelation R₄)
    (u v : Bool) :
    CyclicSatisfiable
        [relabelOutput u R₁, relabelOutput v R₂,
          relabelInput u R₃, relabelInput v R₄] ↔
      CyclicSatisfiable [R₁, R₂, R₃, R₄] := by
  rcases eq_idRel_or_eq_flipRel_of_bijection h₁ with h₁ | h₁ <;>
    rcases eq_idRel_or_eq_flipRel_of_bijection h₂ with h₂ | h₂ <;>
    rcases eq_idRel_or_eq_flipRel_of_bijection h₃ with h₃ | h₃ <;>
    rcases eq_idRel_or_eq_flipRel_of_bijection h₄ with h₄ | h₄
  all_goals
    subst R₁
    subst R₂
    subst R₃
    subst R₄
    cases u <;> cases v <;> native_decide

end BinaryRelationCycle
end HigherRankKUM
