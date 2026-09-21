import HigherRankKUM.Rank4.CyclicWindowFour

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

/-- The moved four-position window itself is unchanged as a set of ground
elements.  A four-block reorder only changes the order inside this basis
window. -/
theorem cyclicWindow_four_eq_at_fourBlock_start
    {E : Set α} {n : ℕ}
    {hn : 0 < n} {σ τ : Fin n ≃ E} {s : Fin n}
    (hmove : FourBlockReorder hn σ τ s) :
    cyclicWindow 4 hn τ s = cyclicWindow 4 hn σ s := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    have hmem :
        τ (cyclicIndex n hn s q.val) ∈
          Set.range (fun r : Fin 4 => τ (cyclicIndex n hn s r.val)) :=
      ⟨q, rfl⟩
    rw [hmove.2] at hmem
    rcases hmem with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    exact congrArg Subtype.val hr
  · rintro ⟨q, rfl⟩
    have hmem :
        σ (cyclicIndex n hn s q.val) ∈
          Set.range (fun r : Fin 4 => σ (cyclicIndex n hn s r.val)) :=
      ⟨q, rfl⟩
    rw [← hmove.2] at hmem
    rcases hmem with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    exact congrArg Subtype.val hr

/-- Consequently the central four-block window remains a base whenever the
original order was a rank-four CBO. -/
theorem isBase_cyclicWindow_four_at_fourBlock_start
    {M : Matroid α} {E : Set α} {n : ℕ}
    {hn : 0 < n} {σ τ : Fin n ≃ E} {s : Fin n}
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hmove : FourBlockReorder hn σ τ s) :
    M.IsBase (cyclicWindow 4 hn τ s) := by
  rw [cyclicWindow_four_eq_at_fourBlock_start hmove]
  exact hσ s

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

/-- Sharpened certification interface: the central moved window is automatic,
and disjoint windows are automatic.  Only overlapping boundary windows whose
start differs from the moved-block start need to be rechecked. -/
theorem cyclicBasisOrder_of_fourBlockReorder_of_boundary_bases
    {M : Matroid α} {E : Set α} {n : ℕ}
    {hn : 0 < n} {σ τ : Fin n ≃ E} {s : Fin n}
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hmove : FourBlockReorder hn σ τ s)
    (hBoundary :
      ∀ i : Fin n,
        i ≠ s →
        ¬ Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s) →
          M.IsBase (cyclicWindow 4 hn τ i)) :
    CyclicBasisOrder M 4 hn τ := by
  intro i
  by_cases his : i = s
  · subst i
    exact isBase_cyclicWindow_four_at_fourBlock_start hσ hmove
  by_cases hdis :
      Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s)
  · rw [cyclicWindow_four_eq_of_disjoint_fourBlockPositions hmove hdis]
    exact hσ i
  · exact hBoundary i his hdis

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
