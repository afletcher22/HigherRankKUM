import HigherRankKUM.Rank4.FourBlockBoundary
import HigherRankKUM.CyclicWindowCardinality

namespace HigherRankKUM
namespace Rank4FourBlockFailure

open Set
open Rank4FourBlockMove

noncomputable section

variable {α : Type*}

/-- If an explicit four-block permutation fails to preserve a rank-four cyclic
basis ordering, then at least one of the six noncentral boundary windows is
not a base.

This is the failure-direction companion to the six-window certification
theorem.  It is the local rigidity interface used downstream: every failed
four-block repair has a witness supported at one of the starts
`s-3,s-2,s-1,s+1,s+2,s+3`. -/
theorem exists_nonbase_boundary_of_not_cyclicBasisOrder_applyFourBlockPerm
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4))
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hfail :
      ¬ CyclicBasisOrder M 4 hn
        (applyFourBlockPerm hn (by omega) σ s π)) :
    ∃ i : Fin n,
      i ∈ fourBlockBoundaryStarts hn s ∧
      ¬ M.IsBase
        (cyclicWindow 4 hn
          (applyFourBlockPerm hn (by omega) σ s π) i) := by
  by_contra hnone
  push_neg at hnone
  apply hfail
  apply cyclicBasisOrder_applyFourBlockPerm_of_six_boundary_bases
    hn h7n σ s π hσ
  · apply hnone
    simp [fourBlockBoundaryStarts]
  · apply hnone
    simp [fourBlockBoundaryStarts]
  · apply hnone
    simp [fourBlockBoundaryStarts]
  · apply hnone
    simp [fourBlockBoundaryStarts]
  · apply hnone
    simp [fourBlockBoundaryStarts]
  · apply hnone
    simp [fourBlockBoundaryStarts]

/-- Abstract-reorder version of the same localization principle. -/
theorem exists_nonbase_boundary_of_not_cyclicBasisOrder_fourBlockReorder
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    {σ τ : Fin n ≃ E} {s : Fin n}
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hmove : FourBlockReorder hn σ τ s)
    (hfail : ¬ CyclicBasisOrder M 4 hn τ) :
    ∃ i : Fin n,
      i ∈ fourBlockBoundaryStarts hn s ∧
      ¬ M.IsBase (cyclicWindow 4 hn τ i) := by
  by_contra hnone
  push_neg at hnone
  apply hfail
  apply cyclicBasisOrder_of_fourBlockReorder_of_six_boundary_bases
    hn h7n hσ hmove
  · apply hnone
    simp [fourBlockBoundaryStarts]
  · apply hnone
    simp [fourBlockBoundaryStarts]
  · apply hnone
    simp [fourBlockBoundaryStarts]
  · apply hnone
    simp [fourBlockBoundaryStarts]
  · apply hnone
    simp [fourBlockBoundaryStarts]
  · apply hnone
    simp [fourBlockBoundaryStarts]


/-- Under the ambient rank-four and ground-set hypotheses, a failed explicit
four-block repair has a genuinely dependent witness among the same six
boundary windows. -/
theorem exists_dep_boundary_of_not_cyclicBasisOrder_applyFourBlockPerm
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h7n : 7 ≤ n)
    (hEsub : E ⊆ M.E)
    (hRank : M.eRank = (4 : ℕ∞))
    (σ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4))
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hfail :
      ¬ CyclicBasisOrder M 4 hn
        (applyFourBlockPerm hn (by omega) σ s π)) :
    ∃ i : Fin n,
      i ∈ fourBlockBoundaryStarts hn s ∧
      M.Dep
        (cyclicWindow 4 hn
          (applyFourBlockPerm hn (by omega) σ s π) i) := by
  obtain ⟨i, hi, hnot⟩ :=
    exists_nonbase_boundary_of_not_cyclicBasisOrder_applyFourBlockPerm
      hn h7n σ s π hσ hfail
  refine ⟨i, hi, ?_⟩
  exact cyclicWindow_four_dep_of_not_isBase
    hn (by omega) hEsub hRank
    (applyFourBlockPerm hn (by omega) σ s π) i hnot

end

end Rank4FourBlockFailure
end HigherRankKUM
