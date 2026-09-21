import HigherRankKUM.Rank4.FiniteSchedule
import HigherRankKUM.Rank4.SaturatedFlatRankThree
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4SaturatedSixDefectSchedule

open Set

noncomputable section

variable {α : Type*}

/-- Slot type for the saturated-flat six-defect schedule:
3k flat slots and k+2 complement slots. -/
abbrev SaturatedSlots (k : ℕ) :=
  Fin (3 * k) ⊕ Fin (k + 2)

/-- One ordinary HHHR block in the repeated prefix. -/
def saturatedPrefixSlot {k : ℕ} (j : Fin (k - 2)) :
    Fin 4 → SaturatedSlots k :=
  ![Sum.inl ⟨3 * j.val, by omega⟩,
    Sum.inl ⟨3 * j.val + 1, by omega⟩,
    Sum.inl ⟨3 * j.val + 2, by omega⟩,
    Sum.inr ⟨j.val, by omega⟩]

/-- Ten-position tail HHHR HR HH RR.

The tail consumes the last six flat slots and last four complement slots. -/
def saturatedTailSlot {k : ℕ} (hk : 2 ≤ k) :
    Fin 10 → SaturatedSlots k :=
  ![Sum.inl ⟨3 * k - 6, by omega⟩,
    Sum.inl ⟨3 * k - 5, by omega⟩,
    Sum.inl ⟨3 * k - 4, by omega⟩,
    Sum.inr ⟨k - 2, by omega⟩,
    Sum.inl ⟨3 * k - 3, by omega⟩,
    Sum.inr ⟨k - 1, by omega⟩,
    Sum.inl ⟨3 * k - 2, by omega⟩,
    Sum.inl ⟨3 * k - 1, by omega⟩,
    Sum.inr ⟨k, by omega⟩,
    Sum.inr ⟨k + 1, by omega⟩]

/-- Uniform HHHR slot formula for the first k-1 four-blocks.

The first k-2 blocks are the repeated prefix, while q=k-2 is the first
HHHR block of the ten-position tail. -/
def saturatedRegularBlockSlot {k : ℕ} (q : Fin (k - 1)) :
    Fin 4 → SaturatedSlots k :=
  ![Sum.inl ⟨3 * q.val, by omega⟩,
    Sum.inl ⟨3 * q.val + 1, by omega⟩,
    Sum.inl ⟨3 * q.val + 2, by omega⟩,
    Sum.inr ⟨q.val, by omega⟩]

/-- Regroup repeated HHHR blocks and the ten-position tail into the flat and
complement slot families. -/
def saturatedRegroupEquiv (k : ℕ) (hk : 2 ≤ k) :
    (Fin (k - 2) × Fin 4) ⊕ Fin 10 ≃ SaturatedSlots k := by
  let f : (Fin (k - 2) × Fin 4) ⊕ Fin 10 → SaturatedSlots k
    | Sum.inl x => saturatedPrefixSlot x.1 x.2
    | Sum.inr r => saturatedTailSlot hk r
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).2
  refine ⟨?_, ?_⟩
  · intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · rcases x with ⟨i, r⟩
      rcases y with ⟨j, s⟩
      fin_cases r <;> fin_cases s <;>
        simp [f, saturatedPrefixSlot, Fin.ext_iff] at hxy ⊢ <;> omega
    · rcases x with ⟨i, r⟩
      fin_cases r <;> fin_cases y <;>
        simp [f, saturatedPrefixSlot, saturatedTailSlot,
          Fin.ext_iff] at hxy <;> omega
    · rcases y with ⟨j, s⟩
      fin_cases x <;> fin_cases s <;>
        simp [f, saturatedPrefixSlot, saturatedTailSlot,
          Fin.ext_iff] at hxy <;> omega
    · fin_cases x <;> fin_cases y <;>
        simp [f, saturatedTailSlot, Fin.ext_iff] at hxy ⊢ <;> omega
  · simp [SaturatedSlots]
    omega

/-- Decompose global positions into k-2 ordinary four-blocks followed by the
ten-position exceptional tail. -/
def saturatedBlockTailEquiv (k : ℕ) (hk : 2 ≤ k) :
    Fin (4 * k + 2) ≃ (Fin (k - 2) × Fin 4) ⊕ Fin 10 := by
  have hcard : (k - 2) * 4 + 10 = 4 * k + 2 := by omega
  exact (finCongr hcard.symm).trans
    ((finSumFinEquiv :
      Fin ((k - 2) * 4) ⊕ Fin 10 ≃
        Fin ((k - 2) * 4 + 10)).symm.trans
      (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _)))

/-- Canonical index equivalence for the six-defect saturated-flat schedule. -/
def saturatedIndexEquiv (k : ℕ) (hk : 2 ≤ k) :
    Fin (4 * k + 2) ≃ SaturatedSlots k :=
  (saturatedBlockTailEquiv k hk).trans (saturatedRegroupEquiv k hk)

@[simp] theorem saturatedBlockTailEquiv_symm_prefix
    (k : ℕ) (hk : 2 ≤ k) (j : Fin (k - 2)) (r : Fin 4) :
    (saturatedBlockTailEquiv k hk).symm (Sum.inl (j, r)) =
      ⟨r.val + 4 * j.val, by omega⟩ := by
  apply Fin.ext
  simp [saturatedBlockTailEquiv, finProdFinEquiv]

@[simp] theorem saturatedBlockTailEquiv_symm_tail
    (k : ℕ) (hk : 2 ≤ k) (r : Fin 10) :
    (saturatedBlockTailEquiv k hk).symm (Sum.inr r) =
      ⟨4 * (k - 2) + r.val, by omega⟩ := by
  apply Fin.ext
  simp [saturatedBlockTailEquiv, Nat.mul_comm]

@[simp] theorem saturatedIndexEquiv_prefix
    (k : ℕ) (hk : 2 ≤ k) (j : Fin (k - 2)) (r : Fin 4) :
    saturatedIndexEquiv k hk ⟨r.val + 4 * j.val, by omega⟩ =
      saturatedPrefixSlot j r := by
  have hbt :
      saturatedBlockTailEquiv k hk
          ⟨r.val + 4 * j.val, by omega⟩ =
        Sum.inl (j, r) := by
    apply (saturatedBlockTailEquiv k hk).symm.injective
    simp
  simp [saturatedIndexEquiv, hbt, saturatedRegroupEquiv]

@[simp] theorem saturatedIndexEquiv_tail
    (k : ℕ) (hk : 2 ≤ k) (r : Fin 10) :
    saturatedIndexEquiv k hk ⟨4 * (k - 2) + r.val, by omega⟩ =
      saturatedTailSlot hk r := by
  have hbt :
      saturatedBlockTailEquiv k hk
          ⟨4 * (k - 2) + r.val, by omega⟩ =
        Sum.inr r := by
    apply (saturatedBlockTailEquiv k hk).symm.injective
    simp
  simp [saturatedIndexEquiv, hbt, saturatedRegroupEquiv]

/-- The first k-1 blocks obey the uniform HHHR indexing formula, including
the first four entries of the exceptional tail. -/
@[simp] theorem saturatedIndexEquiv_regular_block
    (k : ℕ) (hk : 2 ≤ k)
    (q : Fin (k - 1)) (r : Fin 4) :
    saturatedIndexEquiv k hk
        ⟨r.val + 4 * q.val, by omega⟩ =
      saturatedRegularBlockSlot q r := by
  by_cases hq : q.val < k - 2
  · let j : Fin (k - 2) := ⟨q.val, hq⟩
    have hpos :
        (⟨r.val + 4 * q.val, by omega⟩ : Fin (4 * k + 2)) =
          ⟨r.val + 4 * j.val, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hpos, saturatedIndexEquiv_prefix]
    fin_cases r <;>
      simp [saturatedRegularBlockSlot, saturatedPrefixSlot, j]
  · have hqeq : q.val = k - 2 := by omega
    let rt : Fin 10 := ⟨r.val, by omega⟩
    have hpos :
        (⟨r.val + 4 * q.val, by omega⟩ : Fin (4 * k + 2)) =
          ⟨4 * (k - 2) + rt.val, by omega⟩ := by
      apply Fin.ext
      dsimp [rt]
      omega
    rw [hpos, saturatedIndexEquiv_tail]
    fin_cases r <;>
      simp [saturatedRegularBlockSlot, saturatedTailSlot, rt, hqeq]


/-- Concrete interleaving of a flat order and complement order according to
the six-defect schedule. -/
def saturatedScheduleOrder
    {H R : Set α} {k : ℕ}
    (hk : 2 ≤ k)
    (hHR : Disjoint H R)
    (flatOrder : Fin (3 * k) ≃ H)
    (outsideOrder : Fin (k + 2) ≃ R) :
    Fin (4 * k + 2) ≃ (H ∪ R : Set α) := by
  classical
  exact
    (saturatedIndexEquiv k hk).trans
      ((Equiv.sumCongr flatOrder outsideOrder).trans
        (Equiv.Set.union hHR).symm)

/-- Underlying ground element represented by a saturated schedule slot. -/
def saturatedSlotValue
    {H R : Set α} {k : ℕ}
    (flatOrder : Fin (3 * k) ≃ H)
    (outsideOrder : Fin (k + 2) ≃ R) :
    SaturatedSlots k → α
  | Sum.inl i => (flatOrder i : α)
  | Sum.inr j => (outsideOrder j : α)

@[simp] theorem saturatedScheduleOrder_prefix
    {H R : Set α} {k : ℕ}
    (hk : 2 ≤ k)
    (hHR : Disjoint H R)
    (flatOrder : Fin (3 * k) ≃ H)
    (outsideOrder : Fin (k + 2) ≃ R)
    (j : Fin (k - 2)) (r : Fin 4) :
    ((saturatedScheduleOrder hk hHR flatOrder outsideOrder
        ⟨r.val + 4 * j.val, by omega⟩ : (H ∪ R : Set α)) : α) =
      saturatedSlotValue flatOrder outsideOrder
        (saturatedPrefixSlot j r) := by
  classical
  fin_cases r <;>
    simp [saturatedScheduleOrder, saturatedSlotValue, saturatedPrefixSlot]

@[simp] theorem saturatedScheduleOrder_tail
    {H R : Set α} {k : ℕ}
    (hk : 2 ≤ k)
    (hHR : Disjoint H R)
    (flatOrder : Fin (3 * k) ≃ H)
    (outsideOrder : Fin (k + 2) ≃ R)
    (r : Fin 10) :
    ((saturatedScheduleOrder hk hHR flatOrder outsideOrder
        ⟨4 * (k - 2) + r.val, by omega⟩ : (H ∪ R : Set α)) : α) =
      saturatedSlotValue flatOrder outsideOrder
        (saturatedTailSlot hk r) := by
  classical
  fin_cases r <;>
    simp [saturatedScheduleOrder, saturatedSlotValue, saturatedTailSlot]

end

end Rank4SaturatedSixDefectSchedule
end HigherRankKUM
