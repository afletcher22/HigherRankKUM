import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Combinatorics.Matroid.Minor.Contract

namespace HigherRankKUM
namespace BlockerClosure

open Set
open scoped Matroid

variable {α : Type*}

/-- If an element is spanned by two sets whose union is independent, then it
is already spanned by their intersection.

This is the representation-free closure mechanism behind overlapping blocker
windows. -/
theorem mem_closure_inter_of_indep_union
    {M : Matroid α} {X Y : Set α} {e : α}
    (hInd : M.Indep (X ∪ Y))
    (heX : e ∈ M.closure X)
    (heY : e ∈ M.closure Y) :
    e ∈ M.closure (X ∩ Y) := by
  rw [hInd.closure_inter_eq_inter_closure]
  exact ⟨heX, heY⟩

/-- Three successive closure constraints collapse to the common intersection,
provided each adjacent pair of constraint sets has independent union.

For consecutive blocker windows, those adjacent unions sit inside an old basis
window, so this is exactly the induction step needed in rank four. -/
theorem mem_closure_triple_inter_of_adjacent_indep
    {M : Matroid α} {X Y Z : Set α} {e : α}
    (hXY : M.Indep (X ∪ Y))
    (hYZ : M.Indep (Y ∪ Z))
    (heX : e ∈ M.closure X)
    (heY : e ∈ M.closure Y)
    (heZ : e ∈ M.closure Z) :
    e ∈ M.closure (X ∩ Y ∩ Z) := by
  have heXY : e ∈ M.closure (X ∩ Y) :=
    mem_closure_inter_of_indep_union hXY heX heY
  have heYZ : e ∈ M.closure (Y ∩ Z) :=
    mem_closure_inter_of_indep_union hYZ heY heZ
  have hInd :
      M.Indep ((X ∩ Y) ∪ (Y ∩ Z)) := by
    apply hXY.subset
    intro x hx
    rcases hx with hxy | hyz
    · exact Or.inr hxy.2
    · exact Or.inr hyz.1
  have h :=
    mem_closure_inter_of_indep_union hInd heXY heYZ
  have hinter : (X ∩ Y) ∩ (Y ∩ Z) = X ∩ Y ∩ Z := by
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  rw [hinter] at h
  exact h

/-- Four successive closure constraints collapse to their fourfold common
intersection.  This is the abstract form of the rank-four statement that four
consecutive blockers would force the omitted element into the closure of the
empty common window. -/
theorem mem_closure_fourfold_inter_of_adjacent_indep
    {M : Matroid α} {W X Y Z : Set α} {e : α}
    (hWX : M.Indep (W ∪ X))
    (hXY : M.Indep (X ∪ Y))
    (hYZ : M.Indep (Y ∪ Z))
    (heW : e ∈ M.closure W)
    (heX : e ∈ M.closure X)
    (heY : e ∈ M.closure Y)
    (heZ : e ∈ M.closure Z) :
    e ∈ M.closure (W ∩ X ∩ Y ∩ Z) := by
  have heWXY : e ∈ M.closure (W ∩ X ∩ Y) :=
    mem_closure_triple_inter_of_adjacent_indep
      hWX hXY heW heX heY
  have heXYZ : e ∈ M.closure (X ∩ Y ∩ Z) :=
    mem_closure_triple_inter_of_adjacent_indep
      hXY hYZ heX heY heZ
  have hInd :
      M.Indep ((W ∩ X ∩ Y) ∪ (X ∩ Y ∩ Z)) := by
    apply hXY.subset
    intro x hx
    rcases hx with hwxy | hxyz
    · exact Or.inl hwxy.1.2
    · exact Or.inl hxyz.1.1
  have h :=
    mem_closure_inter_of_indep_union hInd heWXY heXYZ
  have hinter :
      (W ∩ X ∩ Y) ∩ (X ∩ Y ∩ Z) = W ∩ X ∩ Y ∩ Z := by
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  rw [hinter] at h
  exact h


/-- For an independent set avoiding a nonloop `e`, being a blocker for `e`
is exactly being dependent after contracting `e`.

This is the formal bridge from the deletion-CBO blocker word to ordinary
rank-three dependence geometry in `M / e`. -/
theorem mem_closure_iff_contractElem_dep
    {M : Matroid α} {T : Set α} {e : α}
    (he : M.IsNonloop e)
    (hT : M.Indep T)
    (heT : e ∉ T) :
    e ∈ M.closure T ↔ (M ／ ({e} : Set α)).Dep T := by
  constructor
  · intro hcl
    have hdepInsert : M.Dep (insert e T) :=
      (hT.mem_closure_iff_of_notMem heT).1 hcl
    have hdis : Disjoint T ({e} : Set α) := by
      rw [Set.disjoint_singleton_right]
      exact heT
    apply he.indep.contract_dep_iff.2
    refine ⟨hdis, ?_⟩
    simpa [Set.union_comm] using hdepInsert
  · intro hdepContract
    have hambient :=
      he.indep.contract_dep_iff.1 hdepContract
    apply (hT.mem_closure_iff_of_notMem heT).2
    simpa [Set.union_comm] using hambient.2



/-- If a basis contains an independent set `T` that already spans `e`, then
the fundamental circuit of `e` with respect to the basis is supported on
`insert e T`. -/
theorem fundCircuit_subset_insert_of_subset_of_mem_closure
    {M : Matroid α} {B T : Set α} {e : α}
    (hB : M.IsBase B)
    (hTB : T ⊆ B)
    (heT : e ∈ M.closure T)
    (heTnot : e ∉ T) :
    M.fundCircuit e B ⊆ insert e T := by
  have hTInd : M.Indep T :=
    hB.indep.subset hTB
  have hCT : M.IsCircuit (M.fundCircuit e T) :=
    hTInd.fundCircuit_isCircuit heT heTnot
  have hCTsubB : M.fundCircuit e T ⊆ insert e B :=
    (M.fundCircuit_subset_insert e T).trans
      (Set.insert_subset_insert hTB)
  have hEq : M.fundCircuit e T = M.fundCircuit e B :=
    hCT.eq_fundCircuit_of_subset hB.indep hCTsubB
  rw [← hEq]
  exact M.fundCircuit_subset_insert e T

/-- If two bases contain the same set `T` and `T` spans `e`, then the
fundamental circuit of `e` is identical in both bases.

For consecutive rank-four basis windows, a blocker triple is such a common
`T`; hence a blocker makes the fundamental circuit persist as the basis
window slides by one position. -/
theorem fundCircuit_eq_of_common_spanning_subset
    {M : Matroid α} {B B' T : Set α} {e : α}
    (hB : M.IsBase B)
    (hB' : M.IsBase B')
    (hTB : T ⊆ B)
    (hTB' : T ⊆ B')
    (heT : e ∈ M.closure T)
    (heTnot : e ∉ T) :
    M.fundCircuit e B = M.fundCircuit e B' := by
  have hTInd : M.Indep T :=
    hB.indep.subset hTB
  have hCT : M.IsCircuit (M.fundCircuit e T) :=
    hTInd.fundCircuit_isCircuit heT heTnot
  have hsubB : M.fundCircuit e T ⊆ insert e B :=
    (M.fundCircuit_subset_insert e T).trans
      (Set.insert_subset_insert hTB)
  have hsubB' : M.fundCircuit e T ⊆ insert e B' :=
    (M.fundCircuit_subset_insert e T).trans
      (Set.insert_subset_insert hTB')
  have hEqB : M.fundCircuit e T = M.fundCircuit e B :=
    hCT.eq_fundCircuit_of_subset hB.indep hsubB
  have hEqB' : M.fundCircuit e T = M.fundCircuit e B' :=
    hCT.eq_fundCircuit_of_subset hB'.indep hsubB'
  exact hEqB.symm.trans hEqB'


/-- Four closure constraints with empty common intersection are impossible for
a nonloop. This is the abstract endpoint behind the rank-four fact that a
blocker word cannot contain four consecutive blockers. -/
theorem not_four_closures_of_nonloop_of_fourfold_inter_empty
    {M : Matroid α} {W X Y Z : Set α} {e : α}
    (he : M.IsNonloop e)
    (hWX : M.Indep (W ∪ X))
    (hXY : M.Indep (X ∪ Y))
    (hYZ : M.Indep (Y ∪ Z))
    (hEmpty : W ∩ X ∩ Y ∩ Z = ∅) :
    ¬ (e ∈ M.closure W ∧
       e ∈ M.closure X ∧
       e ∈ M.closure Y ∧
       e ∈ M.closure Z) := by
  rintro ⟨heW, heX, heY, heZ⟩
  have hmem :=
    mem_closure_fourfold_inter_of_adjacent_indep
      hWX hXY hYZ heW heX heY heZ
  rw [hEmpty, M.closure_empty] at hmem
  exact he.not_isLoop hmem

end BlockerClosure
end HigherRankKUM
