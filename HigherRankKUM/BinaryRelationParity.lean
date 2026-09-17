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

/-- Two pointwise-disjoint bijection relations on `Bool` are exactly the two
complementary perfect matchings: identity/flip in one order or the other. -/
theorem complementary_of_disjoint_bijections
    {R S : Relation}
    (hR : BijectionRelation R) (hS : BijectionRelation S)
    (hdisj : ∀ x y, ¬ (R x y ∧ S x y)) :
    (R = idRel ∧ S = flipRel) ∨ (R = flipRel ∧ S = idRel) := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with rfl | rfl <;>
    rcases eq_idRel_or_eq_flipRel_of_bijection hS with rfl | rfl
  · exfalso
    exact hdisj false false ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exfalso
    exact hdisj false true ⟨by simp [flipRel], by simp [flipRel]⟩

/-- Three Boolean bijections have no cyclic fixed point exactly in the four
odd-parity identity/flip configurations. -/
theorem not_cyclicSatisfiable_three_bijections_iff
    {R S T : Relation}
    (hR : BijectionRelation R) (hS : BijectionRelation S)
    (hT : BijectionRelation T) :
    (¬ CyclicSatisfiable [R, S, T]) ↔
      (R = idRel ∧ S = idRel ∧ T = flipRel) ∨
      (R = idRel ∧ S = flipRel ∧ T = idRel) ∨
      (R = flipRel ∧ S = idRel ∧ T = idRel) ∨
      (R = flipRel ∧ S = flipRel ∧ T = flipRel) := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with hR' | hR' <;>
    rcases eq_idRel_or_eq_flipRel_of_bijection hS with hS' | hS' <;>
    rcases eq_idRel_or_eq_flipRel_of_bijection hT with hT' | hT'
  all_goals
    subst R
    subst S
    subst T
    simp [CyclicSatisfiable, composeList, comp, idRel, flipRel]

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
    cases u <;> cases v <;>
      simp [CyclicSatisfiable, composeList, comp, relabelInput, relabelOutput,
        idRel, flipRel]

end BinaryRelationCycle
end HigherRankKUM
