import HigherRankKUM.BinaryRelationParity

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- Swap both Boolean labels of a relation.  In the rank-four duality
argument this is exactly the operation induced by taking the complement of a
selected endpoint inside each two-element pair. -/
def doubleRelabel (R : Relation) : Relation :=
  relabelInput true (relabelOutput true R)

@[simp] theorem doubleRelabel_apply (R : Relation) (x y : Bool) :
    doubleRelabel R x y ↔ R (Bool.not x) (Bool.not y) := by
  simp [doubleRelabel, relabelInput, relabelOutput]

/-- Simultaneously swapping both endpoint labels preserves full-support
functionality, hence forcedness. -/
theorem doubleRelabel_bijection_iff {R : Relation} :
    BijectionRelation (doubleRelabel R) ↔ BijectionRelation R := by
  constructor
  · rintro ⟨⟨hout, hin⟩, hfun⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x
      obtain ⟨y, hy⟩ := hout (Bool.not x)
      refine ⟨Bool.not y, ?_⟩
      simpa using hy
    · intro y
      obtain ⟨x, hx⟩ := hin (Bool.not y)
      refine ⟨Bool.not x, ?_⟩
      simpa using hx
    · intro x y z hxy hxz
      have h := hfun (x := Bool.not x) (y := Bool.not y) (z := Bool.not z)
        (by simpa using hxy) (by simpa using hxz)
      cases y <;> cases z <;> simp at h ⊢
  · rintro ⟨⟨hout, hin⟩, hfun⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x
      obtain ⟨y, hy⟩ := hout (Bool.not x)
      refine ⟨Bool.not y, ?_⟩
      simpa using hy
    · intro y
      obtain ⟨x, hx⟩ := hin (Bool.not y)
      refine ⟨Bool.not x, ?_⟩
      simpa using hx
    · intro x y z hxy hxz
      have h := hfun (x := Bool.not x) (y := Bool.not y) (z := Bool.not z)
        (by simpa using hxy) (by simpa using hxz)
      cases y <;> cases z <;> simp at h ⊢

/-- Relabelling the input side of a forced Boolean relation preserves
forcedness. -/
theorem relabelInput_bijection (b : Bool) {R : Relation}
    (hR : BijectionRelation R) : BijectionRelation (relabelInput b R) := by
  cases b with
  | false => simpa [relabelInput] using hR
  | true =>
      rcases hR with ⟨⟨hout, hin⟩, hfun⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro x
        obtain ⟨y, hy⟩ := hout (Bool.not x)
        exact ⟨y, by simpa [relabelInput] using hy⟩
      · intro y
        obtain ⟨x, hx⟩ := hin y
        refine ⟨Bool.not x, ?_⟩
        simpa [relabelInput] using hx
      · intro x y z hxy hxz
        exact hfun (by simpa [relabelInput] using hxy)
          (by simpa [relabelInput] using hxz)

/-- Relabelling the output side of a forced Boolean relation preserves
forcedness. -/
theorem relabelOutput_bijection (b : Bool) {R : Relation}
    (hR : BijectionRelation R) : BijectionRelation (relabelOutput b R) := by
  cases b with
  | false => simpa [relabelOutput] using hR
  | true =>
      rcases hR with ⟨⟨hout, hin⟩, hfun⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro x
        obtain ⟨y, hy⟩ := hout x
        refine ⟨Bool.not y, ?_⟩
        simpa [relabelOutput] using hy
      · intro y
        obtain ⟨x, hx⟩ := hin (Bool.not y)
        exact ⟨x, by simpa [relabelOutput] using hx⟩
      · intro x y z hxy hxz
        have h := hfun (by simpa [relabelOutput] using hxy)
          (by simpa [relabelOutput] using hxz)
        cases y <;> cases z <;> simp at h ⊢

/-- Input relabelling preserves forcedness in both directions. -/
theorem relabelInput_bijection_iff (b : Bool) {R : Relation} :
    BijectionRelation (relabelInput b R) ↔ BijectionRelation R := by
  constructor
  · intro h
    have h' := relabelInput_bijection b h
    cases b <;> simpa [relabelInput] using h'
  · exact relabelInput_bijection b

/-- Output relabelling preserves forcedness in both directions. -/
theorem relabelOutput_bijection_iff (b : Bool) {R : Relation} :
    BijectionRelation (relabelOutput b R) ↔ BijectionRelation R := by
  constructor
  · intro h
    have h' := relabelOutput_bijection b h
    cases b <;> simpa [relabelOutput] using h'
  · exact relabelOutput_bijection b

/-- For a forced Boolean transition, swapping the input labels or swapping the
output labels has the same effect.  This is special to the two permutations
`id` and `flip`. -/
theorem relabelInput_eq_relabelOutput_of_bijection
    (b : Bool) {R : Relation} (hR : BijectionRelation R) :
    relabelInput b R = relabelOutput b R := by
  cases b
  · simp [relabelInput, relabelOutput]
  · rcases eq_idRel_or_eq_flipRel_of_bijection hR with rfl | rfl <;>
      funext x y <;> apply propext <;>
      cases x <;> cases y <;> simp [relabelInput, relabelOutput, idRel, flipRel]

/-- Reversing the input convention on all four forced relations does not
change four-cycle parity.  This is the algebraic wrapper needed because
`AdmissiblePairCycle.localRelation` reverses the left pair in every h=2 local
relation. -/
theorem cyclicSatisfiable_four_relabelInput_true
    {R₁ R₂ R₃ R₄ : Relation}
    (h₁ : BijectionRelation R₁) (h₂ : BijectionRelation R₂)
    (h₃ : BijectionRelation R₃) (h₄ : BijectionRelation R₄) :
    CyclicSatisfiable
        [relabelInput true R₁, relabelInput true R₂,
          relabelInput true R₃, relabelInput true R₄] ↔
      CyclicSatisfiable [R₁, R₂, R₃, R₄] := by
  rw [relabelInput_eq_relabelOutput_of_bijection true h₁,
    relabelInput_eq_relabelOutput_of_bijection true h₂]
  exact cyclicSatisfiable_four_relabel h₁ h₂ h₃ h₄ true true

/-- A forced Boolean relation is symmetric: identity and flip are both equal
to their transpose. -/
theorem transpose_eq_self_of_bijection {R : Relation}
    (hR : BijectionRelation R) : transpose R = R := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with rfl | rfl <;> simp

/-- One true cell determines an entire forced Boolean relation. -/
theorem eq_of_bijections_of_shared_cell
    {R S : Relation} (hR : BijectionRelation R) (hS : BijectionRelation S)
    {x y : Bool} (hRxy : R x y) (hSxy : S x y) : R = S := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with h | h <;> subst R <;>
  rcases eq_idRel_or_eq_flipRel_of_bijection hS with h | h <;> subst S
  all_goals
    cases x <;> cases y <;> simp [idRel, flipRel] at hRxy hSxy ⊢

/-- If two forced Boolean relations agree on the `false` output column, they
are equal. -/
theorem eq_of_bijections_of_agree_output_false
    {R S : Relation} (hR : BijectionRelation R) (hS : BijectionRelation S)
    (hagree : ∀ x, R x false ↔ S x false) : R = S := by
  obtain ⟨x, hx⟩ := hR.1.2 false
  exact eq_of_bijections_of_shared_cell hR hS hx ((hagree x).mp hx)

/-- If two forced Boolean relations agree on the `true` input row, they are
equal. -/
theorem eq_of_bijections_of_agree_input_true
    {R S : Relation} (hR : BijectionRelation R) (hS : BijectionRelation S)
    (hagree : ∀ y, R true y ↔ S true y) : R = S := by
  obtain ⟨y, hy⟩ := hR.1.1 true
  exact eq_of_bijections_of_shared_cell hR hS hy ((hagree y).mp hy)

/-- Relabelling every vertex of a three-relation cycle by Boolean negation
preserves cyclic satisfiability.  No forcedness hypothesis is needed. -/
theorem cyclicSatisfiable_three_doubleRelabel
    (R S T : Relation) :
    CyclicSatisfiable [doubleRelabel R, doubleRelabel S, doubleRelabel T] ↔
      CyclicSatisfiable [R, S, T] := by
  constructor
  · intro h
    simp only [CyclicSatisfiable, composeList, comp, idRel] at h ⊢
    rcases h with ⟨x, y, hxy, z, hyz, hzx⟩
    refine ⟨Bool.not x, Bool.not y, ?_, Bool.not z, ?_, ?_⟩
    · simpa using hxy
    · simpa using hyz
    · simpa using hzx
  · intro h
    simp only [CyclicSatisfiable, composeList, comp, idRel] at h ⊢
    rcases h with ⟨x, y, hxy, z, hyz, hzx⟩
    refine ⟨Bool.not x, Bool.not y, ?_, Bool.not z, ?_, ?_⟩
    · simpa using hxy
    · simpa using hyz
    · simpa using hzx

/-- On a forced relation, double relabelling preserves whether the relation is
identity or flip. -/
theorem doubleRelabel_preserves_orientation
    {R : Relation} (hR : BijectionRelation R) :
    (doubleRelabel R = idRel ↔ R = idRel) ∧
    (doubleRelabel R = flipRel ↔ R = flipRel) := by
  simpa [doubleRelabel] using double_relabel_preserves_orientation hR

end BinaryRelationCycle
end HigherRankKUM
