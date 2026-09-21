import HigherRankKUM.Rank4.FourBlockBoundary

namespace HigherRankKUM
namespace Rank4FourBlockAttemptLocality

open Set
open Rank4FourBlockMove

noncomputable section

variable {α : Type*}

/-- The position support needed to decide whether a four-block permutation at
`s` preserves a rank-four cyclic basis ordering.

It is the union of all rank-four position windows meeting the moved block. -/
def fourBlockAttemptSupport
    {n : ℕ} (hn : 0 < n) (s : Fin n) : Set (Fin n) :=
  {j | ∃ i : Fin n,
    ¬ Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s) ∧
      j ∈ cyclicPositionWindow 4 hn i}

theorem mem_fourBlockAttemptSupport_of_affected
    {n : ℕ} {hn : 0 < n} {s i j : Fin n}
    (hi :
      ¬ Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s))
    (hj : j ∈ cyclicPositionWindow 4 hn i) :
    j ∈ fourBlockAttemptSupport hn s := by
  exact ⟨i, hi, hj⟩

/-- Every moved position itself belongs to the attempt support. -/
theorem fourBlockPositions_subset_attemptSupport
    {n : ℕ} (hn : 0 < n) (s : Fin n) :
    fourBlockPositions hn s ⊆ fourBlockAttemptSupport hn s := by
  intro j hj
  refine ⟨s, ?_, ?_⟩
  · apply Set.not_disjoint_iff.mpr
    exact ⟨j, by simpa [fourBlockPositions] using hj, hj⟩
  · simpa [fourBlockPositions] using hj

/-- If `j` lies in an affected rank-four window, then the source position
from which a supported local permutation reads its new entry also lies in the
same attempt support. -/
theorem supportedFourBlockPerm_mem_attemptSupport_of_affected
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n)
    (s : Fin n) (π : Equiv.Perm (Fin 4))
    {i j : Fin n}
    (hi :
      ¬ Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s))
    (hj : j ∈ cyclicPositionWindow 4 hn i) :
    supportedFourBlockPerm hn h4n s π j ∈
      fourBlockAttemptSupport hn s := by
  have hjSupp :
      j ∈ fourBlockAttemptSupport hn s :=
    mem_fourBlockAttemptSupport_of_affected hi hj
  by_cases hjBlock : j ∈ fourBlockPositions hn s
  · rw [← range_fourBlockEmbedding_eq_fourBlockPositions hn h4n s] at hjBlock
    rcases hjBlock with ⟨q, rfl⟩
    rw [supportedFourBlockPerm_apply_block]
    apply fourBlockPositions_subset_attemptSupport hn s
    rw [← range_fourBlockEmbedding_eq_fourBlockPositions hn h4n s]
    exact ⟨π q, rfl⟩
  · rw [supportedFourBlockPerm_apply_outside hn h4n s π hjBlock]
    exact hjSupp

/-- Two deletion orders agreeing on the attempt support give the same entry
after applying the same local permutation at every position of every affected
rank-four window. -/
theorem applyFourBlockPerm_eq_on_affected_position
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ τ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4))
    (hEq :
      ∀ j : Fin n, j ∈ fourBlockAttemptSupport hn s → σ j = τ j)
    {i j : Fin n}
    (hi :
      ¬ Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s))
    (hj : j ∈ cyclicPositionWindow 4 hn i) :
    applyFourBlockPerm hn h4n σ s π j =
      applyFourBlockPerm hn h4n τ s π j := by
  let p := supportedFourBlockPerm hn h4n s π j
  have hp :
      p ∈ fourBlockAttemptSupport hn s := by
    dsimp [p]
    exact supportedFourBlockPerm_mem_attemptSupport_of_affected
      hn h4n s π hi hj
  change σ p = τ p
  exact hEq p hp

/-- Hence the candidate reordered rank-four windows are literally equal on
every affected start. -/
theorem cyclicWindow_four_applyFourBlockPerm_eq_of_eq_on_attemptSupport
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ τ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4))
    (hEq :
      ∀ j : Fin n, j ∈ fourBlockAttemptSupport hn s → σ j = τ j)
    {i : Fin n}
    (hi :
      ¬ Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s)) :
    cyclicWindow 4 hn (applyFourBlockPerm hn h4n σ s π) i =
      cyclicWindow 4 hn (applyFourBlockPerm hn h4n τ s π) i := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨q, ?_⟩
    have hj :
        cyclicIndex n hn i q.val ∈ cyclicPositionWindow 4 hn i :=
      ⟨q, rfl⟩
    exact congrArg Subtype.val
      (applyFourBlockPerm_eq_on_affected_position
        hn h4n σ τ s π hEq hi hj).symm
  · rintro ⟨q, rfl⟩
    refine ⟨q, ?_⟩
    have hj :
        cyclicIndex n hn i q.val ∈ cyclicPositionWindow 4 hn i :=
      ⟨q, rfl⟩
    exact congrArg Subtype.val
      (applyFourBlockPerm_eq_on_affected_position
        hn h4n σ τ s π hEq hi hj)

/-- Locality of four-block attempt validity.

For two rank-four CBOs, whether a fixed local permutation at `s` preserves
the CBO depends only on their entries on `fourBlockAttemptSupport hn s`. -/
theorem cyclicBasisOrder_applyFourBlockPerm_iff_of_eq_on_attemptSupport
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ τ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4))
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hτ : CyclicBasisOrder M 4 hn τ)
    (hEq :
      ∀ j : Fin n, j ∈ fourBlockAttemptSupport hn s → σ j = τ j) :
    CyclicBasisOrder M 4 hn (applyFourBlockPerm hn h4n σ s π) ↔
      CyclicBasisOrder M 4 hn (applyFourBlockPerm hn h4n τ s π) := by
  let σ' := applyFourBlockPerm hn h4n σ s π
  let τ' := applyFourBlockPerm hn h4n τ s π
  have hmoveσ : FourBlockReorder hn σ σ' s := by
    dsimp [σ']
    exact fourBlockReorder_applyFourBlockPerm hn h4n σ s π
  have hmoveτ : FourBlockReorder hn τ τ' s := by
    dsimp [τ']
    exact fourBlockReorder_applyFourBlockPerm hn h4n τ s π
  constructor
  · intro hσ'
    apply (cyclicBasisOrder_fourBlockReorder_iff_affected_bases
      hτ hmoveτ).2
    intro i hi
    have hbaseσ :
        M.IsBase (cyclicWindow 4 hn σ' i) :=
      ((cyclicBasisOrder_fourBlockReorder_iff_affected_bases
        hσ hmoveσ).1 hσ') i hi
    have hwin :
        cyclicWindow 4 hn σ' i = cyclicWindow 4 hn τ' i := by
      dsimp [σ', τ']
      exact
        cyclicWindow_four_applyFourBlockPerm_eq_of_eq_on_attemptSupport
          hn h4n σ τ s π hEq hi
    rwa [← hwin]
  · intro hτ'
    apply (cyclicBasisOrder_fourBlockReorder_iff_affected_bases
      hσ hmoveσ).2
    intro i hi
    have hbaseτ :
        M.IsBase (cyclicWindow 4 hn τ' i) :=
      ((cyclicBasisOrder_fourBlockReorder_iff_affected_bases
        hτ hmoveτ).1 hτ') i hi
    have hwin :
        cyclicWindow 4 hn σ' i = cyclicWindow 4 hn τ' i := by
      dsimp [σ', τ']
      exact
        cyclicWindow_four_applyFourBlockPerm_eq_of_eq_on_attemptSupport
          hn h4n σ τ s π hEq hi
    rwa [hwin]


/-- A remote four-block reorder does not change any entry on the attempt
support of a candidate move whose support is disjoint from the moved block. -/
theorem eq_on_attemptSupport_of_remote_fourBlockReorder
    {E : Set α} {n : ℕ}
    {hn : 0 < n} {σ τ : Fin n ≃ E} {u s : Fin n}
    (hmove : FourBlockReorder hn σ τ u)
    (hdis :
      Disjoint (fourBlockAttemptSupport hn s) (fourBlockPositions hn u)) :
    ∀ j : Fin n, j ∈ fourBlockAttemptSupport hn s → σ j = τ j := by
  intro j hj
  have hjout : j ∉ fourBlockPositions hn u := by
    intro hju
    exact (Set.disjoint_left.mp hdis) hj hju
  exact (hmove.1 j hjout).symm

/-- Remote-reorder invariance of a candidate four-block attempt.

If the block changed by `σ -> τ` is disjoint from the support needed to
decide the candidate move at `s`, then applying the same local permutation at
`s` preserves the CBO for `σ` exactly when it preserves the CBO for `τ`.
This is the abstract locality statement needed for mobility comparisons. -/
theorem cyclicBasisOrder_applyFourBlockPerm_iff_of_remote_reorder
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ τ : Fin n ≃ E) (u s : Fin n)
    (π : Equiv.Perm (Fin 4))
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hτ : CyclicBasisOrder M 4 hn τ)
    (hmove : FourBlockReorder hn σ τ u)
    (hdis :
      Disjoint (fourBlockAttemptSupport hn s) (fourBlockPositions hn u)) :
    CyclicBasisOrder M 4 hn (applyFourBlockPerm hn h4n σ s π) ↔
      CyclicBasisOrder M 4 hn (applyFourBlockPerm hn h4n τ s π) := by
  exact cyclicBasisOrder_applyFourBlockPerm_iff_of_eq_on_attemptSupport
    hn h4n σ τ s π hσ hτ
    (eq_on_attemptSupport_of_remote_fourBlockReorder hmove hdis)

end

end Rank4FourBlockAttemptLocality
end HigherRankKUM
