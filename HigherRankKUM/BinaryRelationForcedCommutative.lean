import HigherRankKUM.BinaryRelationRelabel

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- Relational composition is associative. -/
theorem comp_assoc (R S T : Relation) :
    comp R (comp S T) = comp (comp R S) T := by
  funext x w
  apply propext
  simp only [comp]
  constructor
  · rintro ⟨y, hxy, z, hyz, hzw⟩
    exact ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
  · rintro ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
    exact ⟨y, hxy, z, hyz, hzw⟩

@[simp] theorem comp_idRel_left (R : Relation) : comp idRel R = R := by
  funext x y
  apply propext
  simp [comp, idRel]

@[simp] theorem comp_idRel_right (R : Relation) : comp R idRel = R := by
  funext x y
  apply propext
  simp [comp, idRel]

@[simp] theorem comp_flipRel_flipRel : comp flipRel flipRel = idRel := by
  funext x y
  apply propext
  cases x <;> cases y <;> simp [comp, flipRel, idRel]

/-- Forced Boolean transitions commute.  This is special to the two-state
identity/flip classification and is what makes obstruction parity independent
of the order in which forced local relations are composed. -/
theorem comp_comm_of_bijections
    {R S : Relation} (hR : BijectionRelation R) (hS : BijectionRelation S) :
    comp R S = comp S R := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with rfl | rfl <;>
    rcases eq_idRel_or_eq_flipRel_of_bijection hS with rfl | rfl <;> simp

/-- Composition of forced Boolean transitions is again forced. -/
theorem comp_bijection
    {R S : Relation} (hR : BijectionRelation R) (hS : BijectionRelation S) :
    BijectionRelation (comp R S) := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with rfl | rfl <;>
    rcases eq_idRel_or_eq_flipRel_of_bijection hS with rfl | rfl
  all_goals
    constructor
    · simp [FullSupport, comp, idRel, flipRel]
    · intro x y z hxy hxz
      cases x <;> cases y <;> cases z <;>
        simp [comp, idRel, flipRel] at hxy hxz ⊢

/-- A list of forced Boolean relations composes to another forced Boolean
relation. -/
theorem composeList_bijection
    {Rs : List Relation} (hRs : ∀ R ∈ Rs, BijectionRelation R) :
    BijectionRelation (composeList Rs) := by
  induction Rs with
  | nil =>
      exact ⟨idRel_fullSupport, by
        intro x y z hxy hxz
        simpa [idRel] using hxy.trans hxz.symm⟩
  | cons R Rs ih =>
      have hR : BijectionRelation R := hRs R (by simp)
      have htail : ∀ S ∈ Rs, BijectionRelation S := by
        intro S hS
        exact hRs S (by simp [hS])
      exact comp_bijection hR (ih htail)

/-- Reordering a finite list of forced Boolean transitions does not change its
composed relation. -/
theorem composeList_eq_of_perm_bijections
    {Rs Ss : List Relation} (hperm : Rs.Perm Ss)
    (hRs : ∀ R ∈ Rs, BijectionRelation R) :
    composeList Rs = composeList Ss := by
  induction hperm with
  | nil => rfl
  | @cons R Rs Ss hperm ih =>
      have htail : ∀ S ∈ Rs, BijectionRelation S := by
        intro S hS
        exact hRs S (by simp [hS])
      simp only [composeList]
      rw [ih htail]
  | @swap R S Rs =>
      have hR : BijectionRelation R := hRs R (by simp)
      have hS : BijectionRelation S := hRs S (by simp)
      simp only [composeList]
      rw [← comp_assoc, comp_comm_of_bijections hR hS, comp_assoc]
  | @trans Rs Ss Ts h₁ h₂ ih₁ ih₂ =>
      have hSs : ∀ S ∈ Ss, BijectionRelation S := by
        intro S hS
        exact hRs S ((h₁.mem_iff).2 hS)
      exact (ih₁ hRs).trans (ih₂ hSs)

/-- For a forced Boolean relation, having a fixed point is equivalent to being
the identity relation. -/
theorem exists_fixedPoint_iff_eq_idRel
    {R : Relation} (hR : BijectionRelation R) :
    (∃ x, R x x) ↔ R = idRel := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with h | h
  · subst R
    simp [idRel]
  · subst R
    simp [flipRel, idRel_ne_flipRel]

/-- Two forced Boolean transitions are equal as soon as they agree on whether
a fixed point exists. -/
theorem eq_of_bijections_of_fixedPoint_iff
    {R S : Relation} (hR : BijectionRelation R) (hS : BijectionRelation S)
    (hfix : (∃ x, R x x) ↔ ∃ x, S x x) : R = S := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with hR' | hR' <;>
    rcases eq_idRel_or_eq_flipRel_of_bijection hS with hS' | hS'
  all_goals
    subst R
    subst S
    simp [idRel, flipRel] at hfix ⊢

end BinaryRelationCycle
end HigherRankKUM
