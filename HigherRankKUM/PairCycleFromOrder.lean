import HigherRankKUM.AdmissiblePairCycle
import HigherRankKUM.BalancedInterleave
import Mathlib.Tactic

namespace HigherRankKUM
namespace PairCycleFromOrder

open Set

noncomputable section

variable {α : Type*}

/-- A transparent equivalence from a Boolean slot to the two positions inside
one pair block. -/
def boolFinTwoEquiv : Bool ≃ Fin 2 where
  toFun
    | false => 0
    | true => 1
  invFun
    | ⟨0, _⟩ => false
    | ⟨1, _⟩ => true
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem boolFinTwoEquiv_false :
    boolFinTwoEquiv false = (0 : Fin 2) := rfl

@[simp] theorem boolFinTwoEquiv_true :
    boolFinTwoEquiv true = (1 : Fin 2) := rfl

/-- Group a full cyclic order on 2N ground elements into consecutive
two-element blocks. -/
def pairEquivOfOrder
    {M : Matroid α} {N : ℕ}
    (order : Fin (2 * N) ≃ M.E) :
    Fin N × Bool ≃ M.E :=
  (Equiv.prodCongr (Equiv.refl (Fin N)) boolFinTwoEquiv).trans
    ((blockPositionEquiv 2 N).trans order)

@[simp] theorem pairEquivOfOrder_false
    {M : Matroid α} {N : ℕ}
    (order : Fin (2 * N) ≃ M.E) (i : Fin N) :
    (((pairEquivOfOrder order) (i, false) : M.E) : α) =
      (order (blockPosition 2 N i (0 : Fin 2)) : α) := by
  rfl

@[simp] theorem pairEquivOfOrder_true
    {M : Matroid α} {N : ℕ}
    (order : Fin (2 * N) ≃ M.E) (i : Fin N) :
    (((pairEquivOfOrder order) (i, true) : M.E) : α) =
      (order (blockPosition 2 N i (1 : Fin 2)) : α) := by
  rfl

/-- For the pair partition induced by a full order, the aligned rank-four
window at block i is exactly the union of the two adjacent pair blocks. -/
theorem alignedWindow_pairEquivOfOrder
    {M : Matroid α} {N : ℕ} (hN : 0 < N)
    (order : Fin (2 * N) ≃ M.E) (i : Fin N) :
    AdmissiblePairCycle.alignedWindow (h := 2) hN
        (pairEquivOfOrder order) i =
      ({(order (blockPosition 2 N i (0 : Fin 2)) : M.E).1,
        (order (blockPosition 2 N i (1 : Fin 2)) : M.E).1,
        (order (blockPosition 2 N (cyclicIndex N hN i 1)
          (0 : Fin 2)) : M.E).1,
        (order (blockPosition 2 N (cyclicIndex N hN i 1)
          (1 : Fin 2)) : M.E).1} : Set α) := by
  ext x
  constructor
  · rintro ⟨⟨q, b⟩, rfl⟩
    fin_cases q <;> cases b <;>
      simp [AdmissiblePairCycle.elem, pairEquivOfOrder, blockPosition]
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · subst x
      exact ⟨((0 : Fin 2), false), by
        simp [AdmissiblePairCycle.elem, pairEquivOfOrder, blockPosition]⟩
    · subst x
      exact ⟨((0 : Fin 2), true), by
        simp [AdmissiblePairCycle.elem, pairEquivOfOrder, blockPosition]⟩
    · subst x
      exact ⟨((1 : Fin 2), false), by
        simp [AdmissiblePairCycle.elem, pairEquivOfOrder, blockPosition]⟩
    · subst x
      exact ⟨((1 : Fin 2), true), by
        simp [AdmissiblePairCycle.elem, pairEquivOfOrder, blockPosition]⟩

/-- A full order on 2N elements whose unions of adjacent consecutive pair
blocks are bases canonically determines an admissible rank-four pair cycle. -/
def admissiblePairCycleOfOrder
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (order : Fin (2 * N) ≃ M.E)
    (hGround : M.E.encard = ((2 * N : ℕ) : ℕ∞))
    (hRank : M.eRank = (4 : ℕ∞))
    (hPairBases : ∀ i : Fin N,
      M.IsBase
        ({(order (blockPosition 2 N i (0 : Fin 2)) : M.E).1,
          (order (blockPosition 2 N i (1 : Fin 2)) : M.E).1,
          (order (blockPosition 2 N (cyclicIndex N hN i 1)
            (0 : Fin 2)) : M.E).1,
          (order (blockPosition 2 N (cyclicIndex N hN i 1)
            (1 : Fin 2)) : M.E).1} : Set α)) :
    AdmissiblePairCycle.Data M N 2 hN where
  pairEquiv := pairEquivOfOrder order
  groundSize := hGround
  rankEq := by simpa using hRank
  alignedBase := by
    intro i
    rw [alignedWindow_pairEquivOfOrder hN order i]
    exact hPairBases i

end

end PairCycleFromOrder
end HigherRankKUM
