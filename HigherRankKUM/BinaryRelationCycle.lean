import Mathlib.Data.Bool.Basic

namespace HigherRankKUM
namespace BinaryRelationCycle

abbrev Relation := Bool → Bool → Prop

def FullSupport (R : Relation) : Prop :=
  (∀ x, ∃ y, R x y) ∧ (∀ y, ∃ x, R x y)

def Functional (R : Relation) : Prop :=
  ∀ ⦃x y z⦄, R x y → R x z → y = z

def BijectionRelation (R : Relation) : Prop :=
  FullSupport R ∧ Functional R

def comp (R S : Relation) : Relation :=
  fun x z => ∃ y, R x y ∧ S y z

def idRel : Relation := fun x y => x = y

def composeList : List Relation → Relation
  | [] => idRel
  | R :: Rs => comp R (composeList Rs)

def CyclicSatisfiable (Rs : List Relation) : Prop :=
  ∃ x, composeList Rs x x

lemma idRel_fullSupport : FullSupport idRel := by
  constructor <;> intro x <;> exact ⟨x, rfl⟩

lemma comp_fullSupport {R S : Relation}
    (hR : FullSupport R) (hS : FullSupport S) : FullSupport (comp R S) := by
  constructor
  · intro x
    obtain ⟨y, hxy⟩ := hR.1 x
    obtain ⟨z, hyz⟩ := hS.1 y
    exact ⟨z, y, hxy, hyz⟩
  · intro z
    obtain ⟨y, hyz⟩ := hS.2 z
    obtain ⟨x, hxy⟩ := hR.2 y
    exact ⟨x, y, hxy, hyz⟩

lemma composeList_fullSupport {Rs : List Relation}
    (h : ∀ R ∈ Rs, FullSupport R) : FullSupport (composeList Rs) := by
  induction Rs with
  | nil => exact idRel_fullSupport
  | cons R Rs ih =>
      exact comp_fullSupport (h R (by simp))
        (ih (fun S hS => h S (by simp [hS])))

lemma exists_both_of_not_functional {R : Relation} (hR : ¬ Functional R) :
    ∃ x, R x false ∧ R x true := by
  by_contra h
  apply hR
  intro x y z hxy hxz
  cases y <;> cases z
  · rfl
  · exfalso
    exact h ⟨x, hxy, hxz⟩
  · exfalso
    exact h ⟨x, hxz, hxy⟩
  · rfl

lemma hasFixedPoint_of_not_functional {R : Relation} (hR : ¬ Functional R) :
    ∃ x, R x x := by
  obtain ⟨x, hx0, hx1⟩ := exists_both_of_not_functional hR
  cases x
  · exact ⟨false, hx0⟩
  · exact ⟨true, hx1⟩

lemma not_functional_comp_of_not_functional_left {R S : Relation}
    (hR : ¬ Functional R) (hS : FullSupport S) :
    ¬ Functional (comp R S) := by
  obtain ⟨x, hx0, hx1⟩ := exists_both_of_not_functional hR
  have hx : ∀ y : Bool, R x y := by
    intro y
    cases y <;> assumption
  obtain ⟨y0, hy0⟩ := hS.2 false
  obtain ⟨y1, hy1⟩ := hS.2 true
  intro hfun
  have h0 : comp R S x false := ⟨y0, hx y0, hy0⟩
  have h1 : comp R S x true := ⟨y1, hx y1, hy1⟩
  have h := hfun h0 h1
  cases h

lemma not_functional_comp_of_not_functional_right {R S : Relation}
    (hR : FullSupport R) (hS : ¬ Functional S) :
    ¬ Functional (comp R S) := by
  obtain ⟨y, hy0, hy1⟩ := exists_both_of_not_functional hS
  obtain ⟨x, hxy⟩ := hR.2 y
  intro hfun
  have h0 : comp R S x false := ⟨y, hxy, hy0⟩
  have h1 : comp R S x true := ⟨y, hxy, hy1⟩
  have h := hfun h0 h1
  cases h

lemma functional_left_of_comp {R S : Relation}
    (hS : FullSupport S) (hcomp : Functional (comp R S)) : Functional R := by
  by_contra hR
  exact not_functional_comp_of_not_functional_left hR hS hcomp

lemma functional_right_of_comp {R S : Relation}
    (hR : FullSupport R) (hcomp : Functional (comp R S)) : Functional S := by
  by_contra hS
  exact not_functional_comp_of_not_functional_right hR hS hcomp

lemma all_functional_of_composeList_functional {Rs : List Relation}
    (hfull : ∀ R ∈ Rs, FullSupport R)
    (hfun : Functional (composeList Rs)) :
    ∀ R ∈ Rs, Functional R := by
  induction Rs with
  | nil => simp
  | cons R Rs ih =>
      have hRfull : FullSupport R := hfull R (by simp)
      have hTailFull : FullSupport (composeList Rs) :=
        composeList_fullSupport (fun S hS => hfull S (by simp [hS]))
      have hRfun : Functional R := functional_left_of_comp hTailFull hfun
      have hTailFun : Functional (composeList Rs) := functional_right_of_comp hRfull hfun
      intro S hS
      simp only [List.mem_cons] at hS
      rcases hS with rfl | hS
      · exact hRfun
      · exact ih (fun T hT => hfull T (by simp [hT])) hTailFun S hS

theorem all_bijection_of_not_cyclicSatisfiable {Rs : List Relation}
    (hfull : ∀ R ∈ Rs, FullSupport R)
    (hunsat : ¬ CyclicSatisfiable Rs) :
    ∀ R ∈ Rs, BijectionRelation R := by
  have hcompFun : Functional (composeList Rs) := by
    by_contra hnf
    exact hunsat (hasFixedPoint_of_not_functional hnf)
  intro R hR
  exact ⟨hfull R hR, all_functional_of_composeList_functional hfull hcompFun R hR⟩

theorem cyclicSatisfiable_of_exists_not_bijection {Rs : List Relation}
    (hfull : ∀ R ∈ Rs, FullSupport R)
    (hslack : ∃ R ∈ Rs, ¬ BijectionRelation R) :
    CyclicSatisfiable Rs := by
  by_contra hunsat
  obtain ⟨R, hRmem, hRnot⟩ := hslack
  exact hRnot (all_bijection_of_not_cyclicSatisfiable hfull hunsat R hRmem)

theorem not_cyclicSatisfiable_iff {Rs : List Relation}
    (hfull : ∀ R ∈ Rs, FullSupport R) :
    ¬ CyclicSatisfiable Rs ↔
      (∀ R ∈ Rs, BijectionRelation R) ∧
      (¬ ∃ x, composeList Rs x x) := by
  constructor
  · intro h
    exact ⟨all_bijection_of_not_cyclicSatisfiable hfull h, h⟩
  · rintro ⟨_, hfix⟩
    exact hfix

end BinaryRelationCycle
end HigherRankKUM
