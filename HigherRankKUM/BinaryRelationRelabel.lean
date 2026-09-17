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
