import HigherRankKUM.Rank4.FourBlockMove
import Mathlib.Logic.Equiv.Fintype

namespace HigherRankKUM
namespace Rank4FourBlockMove

open Set

noncomputable section

variable {α : Type*}

/-- The embedding of the four local coordinates into the four cyclic
positions beginning at `s`.

The hypothesis `4 ≤ n` guarantees that the four cyclic offsets are distinct. -/
def fourBlockEmbedding
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n) (s : Fin n) :
    Fin 4 ↪ Fin n where
  toFun q := cyclicIndex n hn s q.val
  inj' := by
    intro a b hab
    apply Fin.ext
    exact cyclicIndex_injective_offsets n hn s
      (by omega) (by omega) hab

@[simp]
theorem fourBlockEmbedding_apply
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n)
    (s : Fin n) (q : Fin 4) :
    fourBlockEmbedding hn h4n s q =
      cyclicIndex n hn s q.val := by
  rfl

theorem range_fourBlockEmbedding_eq_fourBlockPositions
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n) (s : Fin n) :
    Set.range (fourBlockEmbedding hn h4n s) =
      fourBlockPositions hn s := by
  rfl

/-- Extend a permutation of the four local block coordinates to a permutation
of all cyclic positions, acting as the identity outside the moved block. -/
def supportedFourBlockPerm
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n)
    (s : Fin n) (π : Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin n) :=
  π.viaFintypeEmbedding (fourBlockEmbedding hn h4n s)

@[simp]
theorem supportedFourBlockPerm_apply_block
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n)
    (s : Fin n) (π : Equiv.Perm (Fin 4)) (q : Fin 4) :
    supportedFourBlockPerm hn h4n s π
        (fourBlockEmbedding hn h4n s q) =
      fourBlockEmbedding hn h4n s (π q) := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image
    π (fourBlockEmbedding hn h4n s) q

theorem supportedFourBlockPerm_apply_outside
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n)
    (s : Fin n) (π : Equiv.Perm (Fin 4))
    {i : Fin n}
    (hi : i ∉ fourBlockPositions hn s) :
    supportedFourBlockPerm hn h4n s π i = i := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  intro hirange
  apply hi
  rw [← range_fourBlockEmbedding_eq_fourBlockPositions hn h4n s]
  exact hirange

/-- Apply a local four-coordinate permutation to a cyclic enumeration.

The new entry at position `i` is the old entry at the supported position
permutation applied to `i`. -/
def applyFourBlockPerm
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4)) :
    Fin n ≃ E :=
  (supportedFourBlockPerm hn h4n s π).trans σ

@[simp]
theorem applyFourBlockPerm_apply
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4)) (i : Fin n) :
    applyFourBlockPerm hn h4n σ s π i =
      σ (supportedFourBlockPerm hn h4n s π i) := by
  rfl

/-- Every explicitly supported `Fin 4` permutation is an abstract
`FourBlockReorder`. -/
theorem fourBlockReorder_applyFourBlockPerm
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4)) :
    FourBlockReorder hn σ (applyFourBlockPerm hn h4n σ s π) s := by
  refine ⟨?_, ?_⟩
  · intro i hi
    simp [applyFourBlockPerm,
      supportedFourBlockPerm_apply_outside hn h4n s π hi]
  · ext x
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨π q, ?_⟩
      simp [applyFourBlockPerm, fourBlockEmbedding]
    · rintro ⟨q, rfl⟩
      refine ⟨π.symm q, ?_⟩
      simp [applyFourBlockPerm, fourBlockEmbedding]

/-- Outside the moved four-position block, the explicitly permuted order agrees
pointwise with the original order. -/
theorem applyFourBlockPerm_eq_outside
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4))
    {i : Fin n}
    (hi : i ∉ fourBlockPositions hn s) :
    applyFourBlockPerm hn h4n σ s π i = σ i := by
  simp [applyFourBlockPerm,
    supportedFourBlockPerm_apply_outside hn h4n s π hi]

/-- The existing boundary-only certification theorem specializes immediately
to an explicit local `S₄` permutation. -/
theorem cyclicBasisOrder_applyFourBlockPerm_of_boundary_bases
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ : Fin n ≃ E) (s : Fin n)
    (π : Equiv.Perm (Fin 4))
    (hσ : CyclicBasisOrder M 4 hn σ)
    (hBoundary :
      ∀ i : Fin n,
        i ≠ s →
        ¬ Disjoint (cyclicPositionWindow 4 hn i) (fourBlockPositions hn s) →
          M.IsBase
            (cyclicWindow 4 hn
              (applyFourBlockPerm hn h4n σ s π) i)) :
    CyclicBasisOrder M 4 hn
      (applyFourBlockPerm hn h4n σ s π) := by
  exact cyclicBasisOrder_of_fourBlockReorder_of_boundary_bases
    hσ
    (fourBlockReorder_applyFourBlockPerm hn h4n σ s π)
    hBoundary

end

end Rank4FourBlockMove
end HigherRankKUM
