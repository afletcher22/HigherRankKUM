import HigherRankKUM.BinaryRelationRelabel
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Subperm

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

/-- The identity Boolean transition is forced. -/
theorem idRel_bijection : BijectionRelation idRel := by
  refine ⟨idRel_fullSupport, ?_⟩
  intro x y z hxy hxz
  change x = y at hxy
  change x = z at hxz
  exact hxy.symm.trans hxz

/-- The flip Boolean transition is forced. -/
theorem flipRel_bijection : BijectionRelation flipRel := by
  constructor
  · constructor
    · intro x
      exact ⟨Bool.not x, by cases x <;> simp [flipRel]⟩
    · intro y
      exact ⟨Bool.not y, by cases y <;> simp [flipRel]⟩
  · intro x y z hxy hxz
    cases x <;> cases y <;> cases z <;> simp [flipRel] at hxy hxz ⊢

/-- Forced Boolean transitions commute. This is special to the two-state
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
  · simpa using idRel_bijection
  · simpa using flipRel_bijection
  · simpa using flipRel_bijection
  · simpa using idRel_bijection

/-- A list of forced Boolean relations composes to another forced Boolean
relation. -/
theorem composeList_bijection
    {Rs : List Relation} (hRs : ∀ R ∈ Rs, BijectionRelation R) :
    BijectionRelation (composeList Rs) := by
  induction Rs with
  | nil => simpa [composeList] using idRel_bijection
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
      calc
        comp S (comp R (composeList Rs)) =
            comp (comp S R) (composeList Rs) :=
          comp_assoc S R (composeList Rs)
        _ = comp (comp R S) (composeList Rs) :=
          congrArg (fun T => comp T (composeList Rs))
            (comp_comm_of_bijections hS hR)
        _ = comp R (comp S (composeList Rs)) :=
          (comp_assoc R S (composeList Rs)).symm
  | @trans Rs Ss Ts h₁ h₂ ih₁ ih₂ =>
      have hSs : ∀ S ∈ Ss, BijectionRelation S := by
        intro S hS
        exact hRs S ((h₁.mem_iff).2 hS)
      exact (ih₁ hRs).trans (ih₂ hSs)

/-- Composition distributes over concatenation of relation lists. -/
theorem composeList_append (Rs Ss : List Relation) :
    composeList (Rs ++ Ss) = comp (composeList Rs) (composeList Ss) := by
  induction Rs with
  | nil => simp [composeList]
  | cons R Rs ih =>
      simp only [List.cons_append, composeList]
      rw [ih, comp_assoc]

/-- For a forced Boolean relation, having a fixed point is equivalent to being
the identity relation. -/
theorem exists_fixedPoint_iff_eq_idRel
    {R : Relation} (hR : BijectionRelation R) :
    (∃ x, R x x) ↔ R = idRel := by
  rcases eq_idRel_or_eq_flipRel_of_bijection hR with h | h
  · subst R
    simp [idRel]
  · subst R
    simp [flipRel, flipRel_ne_idRel]

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

/-- For lists made entirely of forced Boolean transitions, equivalence of
cyclic satisfiability upgrades to equality of the total composed relation. -/
theorem composeList_eq_of_cyclicSatisfiable_iff_bijections
    {Rs Ss : List Relation}
    (hRs : ∀ R ∈ Rs, BijectionRelation R)
    (hSs : ∀ S ∈ Ss, BijectionRelation S)
    (hcyc : CyclicSatisfiable Rs ↔ CyclicSatisfiable Ss) :
    composeList Rs = composeList Ss := by
  apply eq_of_bijections_of_fixedPoint_iff
    (composeList_bijection hRs) (composeList_bijection hSs)
  simpa [CyclicSatisfiable] using hcyc

/-- Global forced-replacement principle. If the old and new global relation
lists can each be permuted into an affected sublist followed by the same
remainder, then equality of the affected composed transitions implies equality
of the full composed transitions. This removes any dependence on where the
affected relations occur in the successor-orbit order. -/
theorem composeList_eq_of_perm_replacement
    {old new affectedOld affectedNew rest : List Relation}
    (holdPerm : old.Perm (affectedOld ++ rest))
    (hnewPerm : new.Perm (affectedNew ++ rest))
    (hold : ∀ R ∈ old, BijectionRelation R)
    (hnew : ∀ R ∈ new, BijectionRelation R)
    (haffected : composeList affectedOld = composeList affectedNew) :
    composeList old = composeList new := by
  calc
    composeList old = composeList (affectedOld ++ rest) :=
      composeList_eq_of_perm_bijections holdPerm hold
    _ = comp (composeList affectedOld) (composeList rest) :=
      composeList_append affectedOld rest
    _ = comp (composeList affectedNew) (composeList rest) := by rw [haffected]
    _ = composeList (affectedNew ++ rest) :=
      (composeList_append affectedNew rest).symm
    _ = composeList new :=
      (composeList_eq_of_perm_bijections hnewPerm hnew).symm

/-- Index-level form of the global forced-replacement principle.

`I` is any noduplicated list of affected indices. If `old` and `new` are
forced at every index, agree away from `I`, and the product of the relations
at the affected indices is unchanged, then the full `List.ofFn` product is
unchanged. The affected indices need not be consecutive or appear in the same
order as `List.ofFn`; forced Boolean commutativity removes that dependence. -/
theorem composeList_ofFn_eq_of_index_replacement
    {n : ℕ} (old new : Fin n → Relation) (I : List (Fin n))
    (hI : I.Nodup)
    (hold : ∀ i, BijectionRelation (old i))
    (hnew : ∀ i, BijectionRelation (new i))
    (hout : ∀ i, i ∉ I → new i = old i)
    (haffected : composeList (I.map old) = composeList (I.map new)) :
    composeList (List.ofFn old) = composeList (List.ofFn new) := by
  have hsubset : I ⊆ List.finRange n := by
    intro i hi
    simp
  have hsubperm := hI.subperm hsubset
  obtain ⟨l, hlperm, hIsub⟩ := List.subperm_iff.mp hsubperm
  obtain ⟨rest, hrestperm⟩ := hIsub.exists_perm_append
  have hindexPerm : List.Perm (List.finRange n) (I ++ rest) :=
    hlperm.symm.trans hrestperm
  have hnodupAppend : (I ++ rest).Nodup :=
    (List.nodup_finRange n).perm hindexPerm
  have hdis : Disjoint I rest := (List.nodup_append'.1 hnodupAppend).2.2
  have hrestMap : rest.map new = rest.map old := by
    apply List.map_congr_left
    intro i hi
    apply hout i
    intro hiI
    exact List.disjoint_left.1 hdis hiI hi
  have holdPerm : (List.ofFn old).Perm (I.map old ++ rest.map old) := by
    rw [List.ofFn_eq_map, ← List.map_append]
    exact hindexPerm.map old
  have hnewPerm : (List.ofFn new).Perm (I.map new ++ rest.map old) := by
    rw [List.ofFn_eq_map, ← hrestMap, ← List.map_append]
    exact hindexPerm.map new
  have holdList : ∀ R ∈ List.ofFn old, BijectionRelation R := by
    intro R hR
    simp at hR
    obtain ⟨i, rfl⟩ := hR
    exact hold i
  have hnewList : ∀ R ∈ List.ofFn new, BijectionRelation R := by
    intro R hR
    simp at hR
    obtain ⟨i, rfl⟩ := hR
    exact hnew i
  exact composeList_eq_of_perm_replacement
    holdPerm hnewPerm holdList hnewList haffected

end BinaryRelationCycle
end HigherRankKUM
