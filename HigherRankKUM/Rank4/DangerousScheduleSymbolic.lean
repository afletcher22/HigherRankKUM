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
  exact e.trans (Set.equivOfEq hEq)

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

@[simp] theorem adjacentSymbolicOrder_block_c
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) (j : Fin k) :
    (adjacentSymbolicOrder hk hH eC order (Sum.inl (j, (0 : Fin 4))) : α) =
      (eC ⟨j.val, by omega⟩ : α) := by
  simp [adjacentSymbolicOrder, FiniteSchedule.hyperAdjacentRegroupEquiv,
    FiniteSchedule.hyperAdjacentBlockSlot, slotGroundEquiv]

@[simp] theorem adjacentSymbolicOrder_block_g0
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) (j : Fin k) :
    (adjacentSymbolicOrder hk hH eC order (Sum.inl (j, (1 : Fin 4))) : α) =
      (order ⟨3 * j.val, by omega⟩ : α) := by
  simp [adjacentSymbolicOrder, FiniteSchedule.hyperAdjacentRegroupEquiv,
    FiniteSchedule.hyperAdjacentBlockSlot, slotGroundEquiv]

@[simp] theorem adjacentSymbolicOrder_block_g1
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) (j : Fin k) :
    (adjacentSymbolicOrder hk hH eC order (Sum.inl (j, (2 : Fin 4))) : α) =
      (order ⟨3 * j.val + 1, by omega⟩ : α) := by
  simp [adjacentSymbolicOrder, FiniteSchedule.hyperAdjacentRegroupEquiv,
    FiniteSchedule.hyperAdjacentBlockSlot, slotGroundEquiv]

@[simp] theorem adjacentSymbolicOrder_block_g2
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) (j : Fin k) :
    (adjacentSymbolicOrder hk hH eC order (Sum.inl (j, (3 : Fin 4))) : α) =
      (order ⟨3 * j.val + 2, by omega⟩ : α) := by
  simp [adjacentSymbolicOrder, FiniteSchedule.hyperAdjacentRegroupEquiv,
    FiniteSchedule.hyperAdjacentBlockSlot, slotGroundEquiv]

@[simp] theorem adjacentSymbolicOrder_tail_c
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (adjacentSymbolicOrder hk hH eC order (Sum.inr (0 : Fin 2)) : α) =
      (eC ⟨k, by omega⟩ : α) := by
  simp [adjacentSymbolicOrder, FiniteSchedule.hyperAdjacentRegroupEquiv,
    FiniteSchedule.hyperAdjacentTailSlot, slotGroundEquiv]

@[simp] theorem adjacentSymbolicOrder_tail_g
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (adjacentSymbolicOrder hk hH eC order (Sum.inr (1 : Fin 2)) : α) =
      (order ⟨3 * k, by omega⟩ : α) := by
  simp [adjacentSymbolicOrder, FiniteSchedule.hyperAdjacentRegroupEquiv,
    FiniteSchedule.hyperAdjacentTailSlot, slotGroundEquiv]

@[simp] theorem separatedSymbolicOrder_head_c0
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (separatedSymbolicOrder hk hH eC order (Sum.inl (0 : Fin 6)) : α) =
      (eC ⟨0, by omega⟩ : α) := by
  simp [separatedSymbolicOrder, FiniteSchedule.hyperSeparatedRegroupEquiv,
    FiniteSchedule.hyperSeparatedHeadSlot, slotGroundEquiv]

@[simp] theorem separatedSymbolicOrder_head_g0
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (separatedSymbolicOrder hk hH eC order (Sum.inl (1 : Fin 6)) : α) =
      (order ⟨0, by omega⟩ : α) := by
  simp [separatedSymbolicOrder, FiniteSchedule.hyperSeparatedRegroupEquiv,
    FiniteSchedule.hyperSeparatedHeadSlot, slotGroundEquiv]

@[simp] theorem separatedSymbolicOrder_head_g1
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (separatedSymbolicOrder hk hH eC order (Sum.inl (2 : Fin 6)) : α) =
      (order ⟨1, by omega⟩ : α) := by
  simp [separatedSymbolicOrder, FiniteSchedule.hyperSeparatedRegroupEquiv,
    FiniteSchedule.hyperSeparatedHeadSlot, slotGroundEquiv]

@[simp] theorem separatedSymbolicOrder_head_c1
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (separatedSymbolicOrder hk hH eC order (Sum.inl (3 : Fin 6)) : α) =
      (eC ⟨1, by omega⟩ : α) := by
  simp [separatedSymbolicOrder, FiniteSchedule.hyperSeparatedRegroupEquiv,
    FiniteSchedule.hyperSeparatedHeadSlot, slotGroundEquiv]

@[simp] theorem separatedSymbolicOrder_head_g2
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (separatedSymbolicOrder hk hH eC order (Sum.inl (4 : Fin 6)) : α) =
      (order ⟨2, by omega⟩ : α) := by
  simp [separatedSymbolicOrder, FiniteSchedule.hyperSeparatedRegroupEquiv,
    FiniteSchedule.hyperSeparatedHeadSlot, slotGroundEquiv]

@[simp] theorem separatedSymbolicOrder_head_g3
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (separatedSymbolicOrder hk hH eC order (Sum.inl (5 : Fin 6)) : α) =
      (order ⟨3, by omega⟩ : α) := by
  simp [separatedSymbolicOrder, FiniteSchedule.hyperSeparatedRegroupEquiv,
    FiniteSchedule.hyperSeparatedHeadSlot, slotGroundEquiv]

@[simp] theorem separatedSymbolicOrder_block_c
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) (j : Fin (k - 1)) :
    (separatedSymbolicOrder hk hH eC order (Sum.inr (j, (0 : Fin 4))) : α) =
      (eC ⟨j.val + 2, by omega⟩ : α) := by
  simp [separatedSymbolicOrder, FiniteSchedule.hyperSeparatedRegroupEquiv,
    FiniteSchedule.hyperSeparatedBlockSlot, slotGroundEquiv]

@[simp] theorem separatedSymbolicOrder_block_g0
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) (j : Fin (k - 1)) :
    (separatedSymbolicOrder hk hH eC order (Sum.inr (j, (1 : Fin 4))) : α) =
      (order ⟨3 * j.val + 4, by omega⟩ : α) := by
  simp [separatedSymbolicOrder, FiniteSchedule.hyperSeparatedRegroupEquiv,
    FiniteSchedule.hyperSeparatedBlockSlot, slotGroundEquiv]

@[simp] theorem separatedSymbolicOrder_block_g1
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) (j : Fin (k - 1)) :
    (separatedSymbolicOrder hk hH eC order (Sum.inr (j, (2 : Fin 4))) : α) =
      (order ⟨3 * j.val + 5, by omega⟩ : α) := by
  simp [separatedSymbolicOrder, FiniteSchedule.hyperSeparatedRegroupEquiv,
    FiniteSchedule.hyperSeparatedBlockSlot, slotGroundEquiv]

@[simp] theorem separatedSymbolicOrder_block_g2
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) (j : Fin (k - 1)) :
    (separatedSymbolicOrder hk hH eC order (Sum.inr (j, (3 : Fin 4))) : α) =
      (order ⟨3 * j.val + 6, by omega⟩ : α) := by
  simp [separatedSymbolicOrder, FiniteSchedule.hyperSeparatedRegroupEquiv,
    FiniteSchedule.hyperSeparatedBlockSlot, slotGroundEquiv]

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

/-- Prove a transported successor equation using only natural-number index
values. In particular, all metavariables are fixed before arithmetic tactics
run; the symbolic grammar never rewrites with an under-specified Fin index. -/
theorem transportedNext_eq_of_index_value
    {β : Type*} {n : ℕ} (hn : 0 < n) (e : Fin n ≃ β)
    (p q : β)
    (h : ((e.symm p).val + 1) % n = (e.symm q).val) :
    transportedNext hn e p = q := by
  apply e.symm.injective
  apply Fin.ext
  simpa only [transportedNext, transportedCyclicIndex,
    Equiv.symm_apply_apply, cyclicIndex_val] using h

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
  apply transportedNext_eq_of_index_value
  simp only [adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_tail]
  change (0 + 4 * j.val + 1) % (4 * k + 2) = 1 + 4 * j.val
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem adjacentNext_block1
    {k : ℕ} (hk : 1 ≤ k) (j : Fin k) :
    adjacentNext k hk (Sum.inl (j, (1 : Fin 4))) =
      Sum.inl (j, (2 : Fin 4)) := by
  apply transportedNext_eq_of_index_value
  simp only [adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_tail]
  change (1 + 4 * j.val + 1) % (4 * k + 2) = 2 + 4 * j.val
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem adjacentNext_block2
    {k : ℕ} (hk : 1 ≤ k) (j : Fin k) :
    adjacentNext k hk (Sum.inl (j, (2 : Fin 4))) =
      Sum.inl (j, (3 : Fin 4)) := by
  apply transportedNext_eq_of_index_value
  simp only [adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_tail]
  change (2 + 4 * j.val + 1) % (4 * k + 2) = 3 + 4 * j.val
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem adjacentNext_block3_of_lt
    {k : ℕ} (hk : 1 ≤ k) (j : Fin k)
    (hj : j.val + 1 < k) :
    adjacentNext k hk (Sum.inl (j, (3 : Fin 4))) =
      Sum.inl ((⟨j.val + 1, hj⟩ : Fin k), (0 : Fin 4)) := by
  apply transportedNext_eq_of_index_value
  simp only [adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_tail]
  change (3 + 4 * j.val + 1) % (4 * k + 2) = 0 + 4 * (j.val + 1)
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem adjacentNext_block3_of_not_lt
    {k : ℕ} (hk : 1 ≤ k) (j : Fin k)
    (hj : ¬ j.val + 1 < k) :
    adjacentNext k hk (Sum.inl (j, (3 : Fin 4))) =
      Sum.inr (0 : Fin 2) := by
  apply transportedNext_eq_of_index_value
  simp only [adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_tail]
  change (3 + 4 * j.val + 1) % (4 * k + 2) = 4 * k + 0
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem adjacentNext_tail0
    {k : ℕ} (hk : 1 ≤ k) :
    adjacentNext k hk (Sum.inr (0 : Fin 2)) =
      Sum.inr (1 : Fin 2) := by
  apply transportedNext_eq_of_index_value
  simp only [adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_tail]
  change (4 * k + 0 + 1) % (4 * k + 2) = 4 * k + 1
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem adjacentNext_tail1
    {k : ℕ} (hk : 1 ≤ k) :
    adjacentNext k hk (Sum.inr (1 : Fin 2)) =
      Sum.inl ((⟨0, by omega⟩ : Fin k), (0 : Fin 4)) := by
  apply transportedNext_eq_of_index_value
  simp only [adjacentFinAdapter,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_block,
    FiniteSchedule.hyperAdjacentBlockTailEquiv_symm_tail]
  change (4 * k + 1 + 1) % (4 * k + 2) = 0 + 4 * 0
  have hlast : 4 * k + 1 + 1 = 4 * k + 2 := by omega
  rw [hlast, Nat.mod_self]

/-- Successor on separated symbolic positions; all arithmetic remains in the
adapter equations below. -/
def separatedNext (k : ℕ) (hk : 2 ≤ k) :
    SeparatedPos k → SeparatedPos k :=
  transportedNext (by omega) (separatedFinAdapter k hk)

@[simp] theorem transportedNext_separated
    {k : ℕ} (hk : 2 ≤ k) (p : SeparatedPos k) :
    transportedNext (by omega) (separatedFinAdapter k hk) p =
      separatedNext k hk p := by
  rfl

@[simp] theorem separatedNext_head0
    {k : ℕ} (hk : 2 ≤ k) :
    separatedNext k hk (Sum.inl (0 : Fin 6)) = Sum.inl (1 : Fin 6) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (0 + 1) % (4 * k + 2) = 1
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem separatedNext_head1
    {k : ℕ} (hk : 2 ≤ k) :
    separatedNext k hk (Sum.inl (1 : Fin 6)) = Sum.inl (2 : Fin 6) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (1 + 1) % (4 * k + 2) = 2
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem separatedNext_head2
    {k : ℕ} (hk : 2 ≤ k) :
    separatedNext k hk (Sum.inl (2 : Fin 6)) = Sum.inl (3 : Fin 6) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (2 + 1) % (4 * k + 2) = 3
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem separatedNext_head3
    {k : ℕ} (hk : 2 ≤ k) :
    separatedNext k hk (Sum.inl (3 : Fin 6)) = Sum.inl (4 : Fin 6) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (3 + 1) % (4 * k + 2) = 4
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem separatedNext_head4
    {k : ℕ} (hk : 2 ≤ k) :
    separatedNext k hk (Sum.inl (4 : Fin 6)) = Sum.inl (5 : Fin 6) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (4 + 1) % (4 * k + 2) = 5
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem separatedNext_head5
    {k : ℕ} (hk : 2 ≤ k) :
    separatedNext k hk (Sum.inl (5 : Fin 6)) = Sum.inr ((⟨0, by omega⟩ : Fin (k - 1)), (0 : Fin 4)) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (5 + 1) % (4 * k + 2) = 6 + 0 + 4 * 0
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem separatedNext_block0
    {k : ℕ} (hk : 2 ≤ k) (j : Fin (k - 1)) :
    separatedNext k hk (Sum.inr (j, (0 : Fin 4))) = Sum.inr (j, (1 : Fin 4)) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (6 + 0 + 4 * j.val + 1) % (4 * k + 2) = 6 + 1 + 4 * j.val
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem separatedNext_block1
    {k : ℕ} (hk : 2 ≤ k) (j : Fin (k - 1)) :
    separatedNext k hk (Sum.inr (j, (1 : Fin 4))) = Sum.inr (j, (2 : Fin 4)) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (6 + 1 + 4 * j.val + 1) % (4 * k + 2) = 6 + 2 + 4 * j.val
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem separatedNext_block2
    {k : ℕ} (hk : 2 ≤ k) (j : Fin (k - 1)) :
    separatedNext k hk (Sum.inr (j, (2 : Fin 4))) = Sum.inr (j, (3 : Fin 4)) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (6 + 2 + 4 * j.val + 1) % (4 * k + 2) = 6 + 3 + 4 * j.val
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem separatedNext_block3_of_lt
    {k : ℕ} (hk : 2 ≤ k) (j : Fin (k - 1))
    (hj : j.val + 1 < k - 1) :
    separatedNext k hk (Sum.inr (j, (3 : Fin 4))) = Sum.inr ((⟨j.val + 1, hj⟩ : Fin (k - 1)), (0 : Fin 4)) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (6 + 3 + 4 * j.val + 1) % (4 * k + 2) = 6 + 0 + 4 * (j.val + 1)
  rw [Nat.mod_eq_of_lt (by omega)] <;> omega

@[simp] theorem separatedNext_block3_of_not_lt
    {k : ℕ} (hk : 2 ≤ k) (j : Fin (k - 1))
    (hj : ¬ j.val + 1 < k - 1) :
    separatedNext k hk (Sum.inr (j, (3 : Fin 4))) = Sum.inl (0 : Fin 6) := by
  apply transportedNext_eq_of_index_value
  simp only [separatedFinAdapter,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_head,
    FiniteSchedule.hyperSeparatedHeadBlockEquiv_symm_block]
  change (6 + 3 + 4 * j.val + 1) % (4 * k + 2) = 0
  have hlast : 6 + 3 + 4 * j.val + 1 = 4 * k + 2 := by omega
  rw [hlast, Nat.mod_self]

/-- Four symbolic positions obtained by following the successor grammar. -/
theorem transportedWindow_four_next
    {β : Type*} {E : Set α} {n : ℕ}
    (hn : 0 < n) (e : Fin n ≃ β) (τ : β ≃ E) (p : β) :
    transportedWindow 4 hn e τ p =
      {(τ p : α), (τ (transportedNext hn e p) : α),
        (τ (transportedNext hn e (transportedNext hn e p)) : α),
        (τ (transportedNext hn e
          (transportedNext hn e (transportedNext hn e p))) : α)} := by
  rw [transportedWindow_four_eq]
  simp [transportedWindowFour, transportedNext, transportedCyclicIndex_add]

theorem adjacentWindow_four_next
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) (p : AdjacentPos k) :
    transportedWindow 4 (by omega) (adjacentFinAdapter k hk)
        (adjacentSymbolicOrder hk hH eC order) p =
      {(adjacentSymbolicOrder hk hH eC order p : α),
        (adjacentSymbolicOrder hk hH eC order (adjacentNext k hk p) : α),
        (adjacentSymbolicOrder hk hH eC order
          (adjacentNext k hk (adjacentNext k hk p)) : α),
        (adjacentSymbolicOrder hk hH eC order
          (adjacentNext k hk (adjacentNext k hk (adjacentNext k hk p))) : α)} := by
  exact transportedWindow_four_next (by omega) (adjacentFinAdapter k hk)
    (adjacentSymbolicOrder hk hH eC order) p

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
