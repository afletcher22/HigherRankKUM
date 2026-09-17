import HigherRankKUM.BinaryRelationCycle

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- The unique fixed-point-free bijection relation on `Bool`. -/
def flipRel : Relation := fun x y => x ≠ y

/-- Reverse the direction of a Boolean relation. -/
def transpose (R : Relation) : Relation := fun x y => R y x

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

/-- The two Boolean permutation relations are distinct. -/
theorem idRel_ne_flipRel : idRel ≠ flipRel := by
  intro h
  have hff := congrFun (congrFun h false) false
  simpa [idRel, flipRel] using hff

/-- The symmetric form of `idRel_ne_flipRel`. -/
theorem flipRel_ne_idRel : flipRel ≠ idRel := by
  intro h
  exact idRel_ne_flipRel h.symm

/-- A Boolean bijection relation is injective in the input as well as
functional in the output. -/
theorem cofunctional_of_bijection {R : Relation} (hR : BijectionRelation R) :
    ∀ ⦃x₁ x₂ y⦄, R x₁ y → R x₂ y → x₁ = x₂ := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with h | h
  · subst R
    intro x₁ x₂ y h₁ h₂
    simpa [idRel] using h₁.trans h₂.symm
  · subst R
    intro x₁ x₂ y h₁ h₂
    cases x₁ <;> cases x₂ <;> cases y <;> simp [flipRel] at h₁ h₂ ⊢

/-- Transposing a forced Boolean relation preserves forcedness. -/
theorem transpose_bijection {R : Relation} (hR : BijectionRelation R) :
    BijectionRelation (transpose R) := by
  constructor
  · exact ⟨hR.1.2, hR.1.1⟩
  · intro x y z hxy hxz
    exact cofunctional_of_bijection hR hxy hxz

@[simp] theorem transpose_idRel : transpose idRel = idRel := by
  funext x y
  apply propext
  simp [transpose, idRel, eq_comm]

@[simp] theorem transpose_flipRel : transpose flipRel = flipRel := by
  funext x y
  apply propext
  simp [transpose, flipRel, ne_comm]

private theorem double_relabel_idRel :
    relabelInput true (relabelOutput true idRel) = idRel := by
  funext x y
  apply propext
  cases x <;> cases y <;> simp [relabelInput, relabelOutput, idRel]

private theorem double_relabel_flipRel :
    relabelInput true (relabelOutput true flipRel) = flipRel := by
  funext x y
  apply propext
  cases x <;> cases y <;> simp [relabelInput, relabelOutput, flipRel]

/-- Simultaneously swapping the two labels on both sides preserves the two
possible forced orientations. -/
theorem double_relabel_preserves_orientation
    {R : Relation} (hR : BijectionRelation R) :
    (relabelInput true (relabelOutput true R) = idRel ↔ R = idRel) ∧
    (relabelInput true (relabelOutput true R) = flipRel ↔ R = flipRel) := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with h | h
  · subst R
    rw [double_relabel_idRel]
  · subst R
    rw [double_relabel_flipRel]

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
    simp [CyclicSatisfiable, composeList, comp, idRel, flipRel,
      idRel_ne_flipRel, flipRel_ne_idRel]

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
