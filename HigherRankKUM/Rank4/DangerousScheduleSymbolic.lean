import HigherRankKUM.TransportedCycle
import HigherRankKUM.Rank4.FiniteSchedule
import HigherRankKUM.Rank4.CyclicIndexArithmetic
import HigherRankKUM.Rank4.DangerousHyperplaneSelection
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4DangerousScheduleSymbolic

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- Symbolic position type for the adjacent-good pattern
`(C G G G)^k C G`. -/
abbrev AdjacentPos (k : ℕ) :=
  (Fin k × Fin 4) ⊕ Fin 2

/-- Symbolic position type for the separated-good pattern
`C G G C G G (C G G G)^(k-1)`. -/
abbrev SeparatedPos (k : ℕ) :=
  Fin 6 ⊕ (Fin (k - 1) × Fin 4)

/-- Partition the ground into the complement of a dangerous hyperplane and
the hyperplane itself.  This is intentionally independent of finite schedule
indices. -/
def partsEquivGround
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hH : DangerousHyperplane M k H) :
    (M.E \ H : Set α) ⊕ (H : Set α) ≃ M.E := by
  classical
  have hd : Disjoint (M.E \ H) H := disjoint_sdiff_left
  let e : (M.E \ H : Set α) ⊕ (H : Set α) ≃
      ((M.E \ H) ∪ H : Set α) :=
    (Equiv.Set.union hd).symm
  have hEq : (M.E \ H) ∪ H = M.E := by
    rw [sdiff_union_self, union_eq_self_of_subset_right hH.subset_ground]
  exact e.trans (Equiv.setCongr hEq)

@[simp] theorem partsEquivGround_left
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hH : DangerousHyperplane M k H)
    (c : (M.E \ H : Set α)) :
    (partsEquivGround hH (Sum.inl c) : α) = c := by
  simp [partsEquivGround]

@[simp] theorem partsEquivGround_right
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hH : DangerousHyperplane M k H)
    (g : (H : Set α)) :
    (partsEquivGround hH (Sum.inr g) : α) = g := by
  simp [partsEquivGround]

/-- Identity-on-elements transport from a cyclic order on the restriction
ground subtype to the hyperplane subtype itself. -/
def coreEquiv
    {M : Matroid α} {H : Set α} {n : ℕ}
    (order : Fin n ≃ (M.restrict H).E) :
    Fin n ≃ (H : Set α) :=
  order

@[simp] theorem coreEquiv_coe
    {M : Matroid α} {H : Set α} {n : ℕ}
    (order : Fin n ≃ (M.restrict H).E) (i : Fin n) :
    (coreEquiv order i : α) = (order i : α) := by
  rfl

/-- Map complement/core slots to actual ground elements. -/
def slotGroundEquiv
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    FiniteSchedule.HyperplaneSlots k ≃ M.E :=
  (Equiv.sumCongr eC (coreEquiv order)).trans (partsEquivGround hH)

/-- Ground-set enumeration on symbolic adjacent-pattern positions. -/
def adjacentSymbolicOrder
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k)
    (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    AdjacentPos k ≃ M.E :=
  (FiniteSchedule.hyperAdjacentRegroupEquiv k hk).trans
    (slotGroundEquiv hH eC order)

/-- Ground-set enumeration on symbolic separated-pattern positions. -/
def separatedSymbolicOrder
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    SeparatedPos k ≃ M.E :=
  (FiniteSchedule.hyperSeparatedRegroupEquiv k hk).trans
    (slotGroundEquiv hH eC order)

/-- The only place the adjacent symbolic pattern is identified with
`Fin (4*k+2)`. -/
def adjacentFinAdapter (k : ℕ) (hk : 1 ≤ k) :
    Fin (4 * k + 2) ≃ AdjacentPos k :=
  FiniteSchedule.hyperAdjacentBlockTailEquiv k hk

/-- The only place the separated symbolic pattern is identified with
`Fin (4*k+2)`. -/
def separatedFinAdapter (k : ℕ) (hk : 2 ≤ k) :
    Fin (4 * k + 2) ≃ SeparatedPos k :=
  FiniteSchedule.hyperSeparatedHeadBlockEquiv k hk

/-- Symbolic successor for the adjacent-good pattern.  Its definition is
transported from the finite cycle, while the lemmas below expose the finite
state machine seen by schedule proofs. -/
def adjacentNext (k : ℕ) (hk : 1 ≤ k) :
    AdjacentPos k → AdjacentPos k :=
  transportedNext (by omega) (adjacentFinAdapter k hk)

@[simp] theorem adjacentNext_block0
    {k : ℕ} (hk : 1 ≤ k) (j : Fin k) :
    adjacentNext k hk (Sum.inl (j, (0 : Fin 4))) =
      Sum.inl (j, (1 : Fin 4)) := by
  apply (adjacentFinAdapter k hk).symm.injective
  simp only [adjacentNext, transportedNext, transportedCyclicIndex,
    Equiv.symm_apply_apply, adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block]
  rw [cyclicIndex_eq_mk_add_of_lt _ _ _ _ (by omega)]
  apply Fin.ext
  omega

@[simp] theorem adjacentNext_block1
    {k : ℕ} (hk : 1 ≤ k) (j : Fin k) :
    adjacentNext k hk (Sum.inl (j, (1 : Fin 4))) =
      Sum.inl (j, (2 : Fin 4)) := by
  apply (adjacentFinAdapter k hk).symm.injective
  simp only [adjacentNext, transportedNext, transportedCyclicIndex,
    Equiv.symm_apply_apply, adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block]
  rw [cyclicIndex_eq_mk_add_of_lt _ _ _ _ (by omega)]
  apply Fin.ext
  omega

@[simp] theorem adjacentNext_block2
    {k : ℕ} (hk : 1 ≤ k) (j : Fin k) :
    adjacentNext k hk (Sum.inl (j, (2 : Fin 4))) =
      Sum.inl (j, (3 : Fin 4)) := by
  apply (adjacentFinAdapter k hk).symm.injective
  simp only [adjacentNext, transportedNext, transportedCyclicIndex,
    Equiv.symm_apply_apply, adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block]
  rw [cyclicIndex_eq_mk_add_of_lt _ _ _ _ (by omega)]
  apply Fin.ext
  omega

@[simp] theorem adjacentNext_block3_of_lt
    {k : ℕ} (hk : 1 ≤ k) (j : Fin k)
    (hj : j.val + 1 < k) :
    adjacentNext k hk (Sum.inl (j, (3 : Fin 4))) =
      Sum.inl ((⟨j.val + 1, hj⟩ : Fin k), (0 : Fin 4)) := by
  apply (adjacentFinAdapter k hk).symm.injective
  simp only [adjacentNext, transportedNext, transportedCyclicIndex,
    Equiv.symm_apply_apply, adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block]
  rw [cyclicIndex_eq_mk_add_of_lt _ _ _ _ (by omega)]
  apply Fin.ext
  omega

@[simp] theorem adjacentNext_block3_of_not_lt
    {k : ℕ} (hk : 1 ≤ k) (j : Fin k)
    (hj : ¬ j.val + 1 < k) :
    adjacentNext k hk (Sum.inl (j, (3 : Fin 4))) =
      Sum.inr (0 : Fin 2) := by
  apply (adjacentFinAdapter k hk).symm.injective
  simp only [adjacentNext, transportedNext, transportedCyclicIndex,
    Equiv.symm_apply_apply, adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_tail]
  rw [cyclicIndex_eq_mk_add_of_lt _ _ _ _ (by omega)]
  apply Fin.ext
  omega

@[simp] theorem adjacentNext_tail0
    {k : ℕ} (hk : 1 ≤ k) :
    adjacentNext k hk (Sum.inr (0 : Fin 2)) =
      Sum.inr (1 : Fin 2) := by
  apply (adjacentFinAdapter k hk).symm.injective
  simp only [adjacentNext, transportedNext, transportedCyclicIndex,
    Equiv.symm_apply_apply, adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_tail]
  rw [cyclicIndex_eq_mk_add_of_lt _ _ _ _ (by omega)]
  apply Fin.ext
  omega

@[simp] theorem adjacentNext_tail1
    {k : ℕ} (hk : 1 ≤ k) :
    adjacentNext k hk (Sum.inr (1 : Fin 2)) =
      Sum.inl ((⟨0, by omega⟩ : Fin k), (0 : Fin 4)) := by
  apply (adjacentFinAdapter k hk).symm.injective
  simp only [adjacentNext, transportedNext, transportedCyclicIndex,
    Equiv.symm_apply_apply, adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_tail,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block]
  rw [cyclicIndex_eq_mk_sub_of_ge_of_lt_two_mul _ _ _ _
    (by omega) (by omega)]
  apply Fin.ext
  omega

/-- Final adjacent schedule, factored as finite adapter followed by the
symbolic ground order. -/
def adjacentOrder
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k)
    (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    Fin (4 * k + 2) ≃ M.E :=
  (adjacentFinAdapter k hk).trans
    (adjacentSymbolicOrder hk hH eC order)

/-- Final separated schedule, factored as finite adapter followed by the
symbolic ground order. -/
def separatedOrder
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    Fin (4 * k + 2) ≃ M.E :=
  (separatedFinAdapter k hk).trans
    (separatedSymbolicOrder hk hH eC order)

/-- Once all adjacent-pattern symbolic four-windows are bases, the actual
finite schedule is a cyclic basis order. -/
theorem adjacent_cbo_of_symbolic_windows
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k)
    (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hbase : ∀ p : AdjacentPos k,
      M.IsBase
        (transportedWindow 4 (by omega)
          (adjacentFinAdapter k hk)
          (adjacentSymbolicOrder hk hH eC order) p)) :
    CyclicBasisOrder M 4 (by omega)
      (adjacentOrder hk hH eC order) := by
  simpa [adjacentOrder] using
    cyclicBasisOrder_of_transport M (by omega)
      (adjacentFinAdapter k hk)
      (adjacentSymbolicOrder hk hH eC order) hbase

/-- Once all separated-pattern symbolic four-windows are bases, the actual
finite schedule is a cyclic basis order. -/
theorem separated_cbo_of_symbolic_windows
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hbase : ∀ p : SeparatedPos k,
      M.IsBase
        (transportedWindow 4 (by omega)
          (separatedFinAdapter k hk)
          (separatedSymbolicOrder hk hH eC order) p)) :
    CyclicBasisOrder M 4 (by omega)
      (separatedOrder hk hH eC order) := by
  simpa [separatedOrder] using
    cyclicBasisOrder_of_transport M (by omega)
      (separatedFinAdapter k hk)
      (separatedSymbolicOrder hk hH eC order) hbase

end

end Rank4DangerousScheduleSymbolic
end HigherRankKUM
