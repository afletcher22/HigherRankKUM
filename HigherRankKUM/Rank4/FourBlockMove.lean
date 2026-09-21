import HigherRankKUM.Rank4.CyclicWindowFour
import Mathlib.Logic.Equiv.Fintype

namespace HigherRankKUM
namespace Rank4FourBlockMove

open Set

noncomputable section

variable {α : Type*}

/-- The cyclic set of positions in a length-`r` position window.  Unlike
`cyclicWindow`, this records indices rather than ground elements. -/
def cyclicPositionWindow
    {n : ℕ} (r : ℕ) (hn : 0 < n) (i : Fin n) : Set (Fin n) :=
  Set.range fun q : Fin r => cyclicIndex n hn i q.val

/-- The four positions modified by a consecutive four-block reorder. -/
def fourBlockPositions
    {n : ℕ} (hn : 0 < n) (s : Fin n) : Set (Fin n) :=
  cyclicPositionWindow 4 hn s

/-- Two cyclic enumerations differ by a four-block reorder at `s` if:

* they agree at every position outside the four consecutive positions
  beginning at `s`; and
* the four ground elements occupying the affected positions are the same
  before and after the move.

Since both `σ` and `τ` are equivalences, the second condition says exactly
that the affected four entries have been permuted, without choosing a
particular element of `S₄`. -/
def FourBlockReorder
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ τ : Fin n ≃ E) (s : Fin n) : Prop :=
  (∀ i : Fin n, i ∉ fourBlockPositions hn s → τ i = σ i) ∧
  Set.range (fun q : Fin 4 => τ (cyclicIndex n hn s q.val)) =
    Set.range (fun q : Fin 4 => σ (cyclicIndex n hn s q.val))

theorem FourBlockReorder.symm
    {E : Set α} {n : ℕ}
    {hn : 0 < n} {σ τ : Fin n ≃ E} {s : Fin n}
    (h : FourBlockReorder hn σ τ s) :
    FourBlockReorder hn τ σ s := by
  refine ⟨?_, h.2.symm⟩
  intro i hi
  exact (h.1 i hi).symm

/-- If a rank-four window uses none of the four moved positions, then its set
of ground elements is literally unchanged by the four-block reorder. -/
theorem cyclicWindow_four_eq_of_disjoint_fourBlockPositions
    {E : Set α} {n : ℕ}
    {hn : 0 < n} {σ τ : Fin n ≃ E} {s i : Fin n}
    (hmove : FourBlockReorder hn σ τ s)
    (hdis :
      Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s)) :
    cyclicWindow 4 hn τ i = cyclicWindow 4 hn σ i := by
  rw [Set.disjoint_left] at hdis
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨q, ?_⟩
    let j := cyclicIndex n hn i q.val
    have hjpos : j ∈ cyclicPositionWindow 4 hn i := by
      exact ⟨q, rfl⟩
    have hjout : j ∉ fourBlockPositions hn s := by
      intro hjmove
      exact hdis hjpos hjmove
    have heq : τ j = σ j := hmove.1 j hjout
    exact congrArg Subtype.val heq.symm
  · rintro ⟨q, rfl⟩
    refine ⟨q, ?_⟩
    let j := cyclicIndex n hn i q.val
    have hjpos : j ∈ cyclicPositionWindow 4 hn i := by
      exact ⟨q, rfl⟩
    have hjout : j ∉ fourBlockPositions hn s := by
      intro hjmove
      exact hdis hjpos hjmove
    have heq : τ j = σ j := hmove.1 j hjout
    exact congrArg Subtype.val heq

/-- The embedding of `Fin 4` into the four consecutive cyclic positions
beginning at `s`. -/
def fourBlockEmbedding
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n) (s : Fin n) :
    Fin 4 ↪ Fin n where
  toFun q := cyclicIndex n hn s q.val
  inj' := by
    intro a b hab
    apply Fin.ext
    exact cyclicIndex_injective_offsets n hn s
      (by omega) (by omega) hab

@[simp] theorem fourBlockEmbedding_apply
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n) (s : Fin n) (q : Fin 4) :
    fourBlockEmbedding hn h4n s q = cyclicIndex n hn s q.val := rfl

theorem range_fourBlockEmbedding
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n) (s : Fin n) :
    Set.range (fourBlockEmbedding hn h4n s) = fourBlockPositions hn s := by
  rfl

/-- Extend a permutation of the four local slots to the full cyclic position
set, fixing every position outside the chosen four-block. -/
def fourBlockPositionPerm
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n) (s : Fin n)
    (p : Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin n) :=
  p.viaFintypeEmbedding (fourBlockEmbedding hn h4n s)

@[simp] theorem fourBlockPositionPerm_apply_local
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n) (s : Fin n)
    (p : Equiv.Perm (Fin 4)) (q : Fin 4) :
    fourBlockPositionPerm hn h4n s p (cyclicIndex n hn s q.val) =
      cyclicIndex n hn s (p q).val := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image
    p (fourBlockEmbedding hn h4n s) q

theorem fourBlockPositionPerm_apply_outside
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n) (s : Fin n)
    (p : Equiv.Perm (Fin 4)) (i : Fin n)
    (hi : i ∉ fourBlockPositions hn s) :
    fourBlockPositionPerm hn h4n s p i = i := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  simpa [range_fourBlockEmbedding hn h4n s] using hi

/-- The concrete order obtained by applying a local `S₄` permutation to the
four cyclic positions beginning at `s`. -/
def reorderFourBlock
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) (p : Equiv.Perm (Fin 4)) :
    Fin n ≃ E :=
  (fourBlockPositionPerm hn h4n s p).trans σ

@[simp] theorem reorderFourBlock_apply_local
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) (p : Equiv.Perm (Fin 4))
    (q : Fin 4) :
    reorderFourBlock hn h4n σ s p (cyclicIndex n hn s q.val) =
      σ (cyclicIndex n hn s (p q).val) := by
  simp [reorderFourBlock, fourBlockPositionPerm_apply_local]

theorem reorderFourBlock_apply_outside
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) (p : Equiv.Perm (Fin 4))
    (i : Fin n) (hi : i ∉ fourBlockPositions hn s) :
    reorderFourBlock hn h4n σ s p i = σ i := by
  simp [reorderFourBlock,
    fourBlockPositionPerm_apply_outside hn h4n s p i hi]

/-- Every concrete local permutation induces the abstract four-block reorder
relation. -/
theorem reorderFourBlock_isFourBlockReorder
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n) (p : Equiv.Perm (Fin 4)) :
    FourBlockReorder hn σ (reorderFourBlock hn h4n σ s p) s := by
  refine ⟨?_, ?_⟩
  · intro i hi
    exact reorderFourBlock_apply_outside hn h4n σ s p i hi
  · ext x
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨p q, ?_⟩
      exact congrArg Subtype.val
        (reorderFourBlock_apply_local hn h4n σ s p q)
    · rintro ⟨q, rfl⟩
      refine ⟨p.symm q, ?_⟩
      have h :=
        reorderFourBlock_apply_local hn h4n σ s p (p.symm q)
      simpa using congrArg Subtype.val h

/-- A four-block reorder preserves a rank-four cyclic basis ordering once the
finitely many rank-four windows meeting the moved position block have been
rechecked.

This deliberately leaves the affected-start set abstract.  A later local
support lemma can identify it explicitly; the global CBO proof needs only the
disjoint/affected dichotomy. -/
theorem cyclicBasisOrder_of_fourBlockReorder_of_affected_bases
    {M : Matroid α} {E : Set α} {n : ℕ}
    {hn : 0 < n} {σ τ : Fin n ≃ E} {s : Fin n}
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hmove : FourBlockReorder hn σ τ s)
    (hAffected :
      ∀ i : Fin n,
        ¬ Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s) →
          M.IsBase (cyclicWindow 4 hn τ i)) :
    CyclicBasisOrder M 4 hn τ := by
  intro i
  by_cases hdis :
      Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s)
  · rw [cyclicWindow_four_eq_of_disjoint_fourBlockPositions hmove hdis]
    exact hσ i
  · exact hAffected i hdis

/-- Equivalent packaging: after a four-block reorder, CBO certification reduces
to checking only the windows whose position support meets the moved block. -/
theorem cyclicBasisOrder_fourBlockReorder_iff_affected_bases
    {M : Matroid α} {E : Set α} {n : ℕ}
    {hn : 0 < n} {σ τ : Fin n ≃ E} {s : Fin n}
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hmove : FourBlockReorder hn σ τ s) :
    CyclicBasisOrder M 4 hn τ ↔
      ∀ i : Fin n,
        ¬ Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s) →
          M.IsBase (cyclicWindow 4 hn τ i) := by
  constructor
  · intro hτ i hi
    exact hτ i
  · intro h
    exact cyclicBasisOrder_of_fourBlockReorder_of_affected_bases hσ hmove h

end

end Rank4FourBlockMove
end HigherRankKUM
