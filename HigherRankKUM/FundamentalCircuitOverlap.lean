import HigherRankKUM.BlockerClosure

namespace HigherRankKUM

open Set
open scoped Matroid

variable {α : Type*}

/-- For two bases avoiding a ground element `e`, their fundamental circuits
of `e` agree exactly when their common intersection spans `e`.

This is the converse companion to
`BlockerClosure.fundCircuit_eq_of_common_spanning_subset`. -/
theorem fundCircuit_eq_iff_mem_closure_inter_of_bases
    {M : Matroid α} {B B' : Set α} {e : α}
    (hB : M.IsBase B) (hB' : M.IsBase B')
    (heE : e ∈ M.E) (heB : e ∉ B) (heB' : e ∉ B') :
    M.fundCircuit e B = M.fundCircuit e B' ↔
      e ∈ M.closure (B ∩ B') := by
  constructor
  · intro heq
    have heclB : e ∈ M.closure B := by
      simpa [hB.closure_eq] using heE
    have hC : M.IsCircuit (M.fundCircuit e B) :=
      hB.indep.fundCircuit_isCircuit heclB heB
    have heC : e ∈ M.fundCircuit e B :=
      M.mem_fundCircuit e B
    have heInter : e ∉ B ∩ B' := by
      intro he
      exact heB he.1
    apply (M.mem_closure_iff_exists_isCircuit heInter).2
    refine ⟨M.fundCircuit e B, ?_, hC, heC⟩
    intro x hx
    have hxB : x ∈ insert e B :=
      (M.fundCircuit_subset_insert e B) hx
    have hxC' : x ∈ M.fundCircuit e B' := by
      rw [← heq]
      exact hx
    have hxB' : x ∈ insert e B' :=
      (M.fundCircuit_subset_insert e B') hxC'
    simp only [Set.mem_insert_iff] at hxB hxB' ⊢
    rcases hxB with hxe | hxB
    · exact Or.inl hxe
    rcases hxB' with hxe | hxB'
    · exact Or.inl hxe
    · exact Or.inr ⟨hxB, hxB'⟩
  · intro heInter
    exact BlockerClosure.fundCircuit_eq_of_common_spanning_subset
      hB hB' Set.inter_subset_left Set.inter_subset_right heInter
      (by
        intro he
        exact heB he.1)

end HigherRankKUM
