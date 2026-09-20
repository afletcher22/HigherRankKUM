import Mathlib.Combinatorics.Matroid.Closure

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

end BlockerClosure
end HigherRankKUM
