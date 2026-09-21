import HigherRankKUM.Rank4.FourBlockPerm
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4SevenMoveTypes

open Rank4FourBlockMove

noncomputable section

/-- Swap the first two local positions: (1,0,2,3). -/
def swap01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1

/-- Swap the middle two local positions: (0,2,1,3). -/
def swap12 : Equiv.Perm (Fin 4) := Equiv.swap 1 2

/-- Swap the last two local positions: (0,1,3,2). -/
def swap23 : Equiv.Perm (Fin 4) := Equiv.swap 2 3

/-- The canonical half-block exchange: (2,3,0,1). -/
def pairShift : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2 * Equiv.swap 1 3

/-- The second canonical pattern: (2,3,1,0). -/
def canonicalTwist : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * pairShift

/-- Swap the two endpoints of the local block: (3,1,2,0). -/
def endpointSwap : Equiv.Perm (Fin 4) := Equiv.swap 0 3

/-- The seventh move isolated by the historical fixed-e audit:
swap local positions one and three, giving (0,3,2,1). -/
def sideSwap : Equiv.Perm (Fin 4) := Equiv.swap 1 3

theorem swap01_table :
    swap01 0 = 1 ∧ swap01 1 = 0 ∧
    swap01 2 = 2 ∧ swap01 3 = 3 := by
  native_decide

theorem swap12_table :
    swap12 0 = 0 ∧ swap12 1 = 2 ∧
    swap12 2 = 1 ∧ swap12 3 = 3 := by
  native_decide

theorem swap23_table :
    swap23 0 = 0 ∧ swap23 1 = 1 ∧
    swap23 2 = 3 ∧ swap23 3 = 2 := by
  native_decide

theorem pairShift_table :
    pairShift 0 = 2 ∧ pairShift 1 = 3 ∧
    pairShift 2 = 0 ∧ pairShift 3 = 1 := by
  native_decide

theorem canonicalTwist_table :
    canonicalTwist 0 = 2 ∧ canonicalTwist 1 = 3 ∧
    canonicalTwist 2 = 1 ∧ canonicalTwist 3 = 0 := by
  native_decide

theorem endpointSwap_table :
    endpointSwap 0 = 3 ∧ endpointSwap 1 = 1 ∧
    endpointSwap 2 = 2 ∧ endpointSwap 3 = 0 := by
  native_decide

theorem sideSwap_table :
    sideSwap 0 = 0 ∧ sideSwap 1 = 3 ∧
    sideSwap 2 = 2 ∧ sideSwap 3 = 1 := by
  native_decide

@[simp] theorem endpointSwap_zero : endpointSwap 0 = 3 := by native_decide
@[simp] theorem endpointSwap_one : endpointSwap 1 = 1 := by native_decide
@[simp] theorem endpointSwap_two : endpointSwap 2 = 2 := by native_decide
@[simp] theorem endpointSwap_three : endpointSwap 3 = 0 := by native_decide

@[simp] theorem sideSwap_zero : sideSwap 0 = 0 := by native_decide
@[simp] theorem sideSwap_one : sideSwap 1 = 3 := by native_decide
@[simp] theorem sideSwap_two : sideSwap 2 = 2 := by native_decide
@[simp] theorem sideSwap_three : sideSwap 3 = 1 := by native_decide

/-- Concrete action of the endpoint swap on the four moved cyclic positions. -/
theorem apply_endpointSwap_local
    {alpha : Type*} {E : Set alpha} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (sigma : Fin n ≃ E) (s : Fin n) :
    applyFourBlockPerm hn h4n sigma s endpointSwap
        (cyclicIndex n hn s 0) = sigma (cyclicIndex n hn s 3) ∧
    applyFourBlockPerm hn h4n sigma s endpointSwap
        (cyclicIndex n hn s 1) = sigma (cyclicIndex n hn s 1) ∧
    applyFourBlockPerm hn h4n sigma s endpointSwap
        (cyclicIndex n hn s 2) = sigma (cyclicIndex n hn s 2) ∧
    applyFourBlockPerm hn h4n sigma s endpointSwap
        (cyclicIndex n hn s 3) = sigma (cyclicIndex n hn s 0) := by
  constructor
  · simpa using
      (applyFourBlockPerm_apply_local hn h4n sigma s endpointSwap (0 : Fin 4))
  constructor
  · simpa using
      (applyFourBlockPerm_apply_local hn h4n sigma s endpointSwap (1 : Fin 4))
  constructor
  · simpa using
      (applyFourBlockPerm_apply_local hn h4n sigma s endpointSwap (2 : Fin 4))
  · simpa using
      (applyFourBlockPerm_apply_local hn h4n sigma s endpointSwap (3 : Fin 4))

/-- Concrete action of the side swap on the four moved cyclic positions. -/
theorem apply_sideSwap_local
    {alpha : Type*} {E : Set alpha} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (sigma : Fin n ≃ E) (s : Fin n) :
    applyFourBlockPerm hn h4n sigma s sideSwap
        (cyclicIndex n hn s 0) = sigma (cyclicIndex n hn s 0) ∧
    applyFourBlockPerm hn h4n sigma s sideSwap
        (cyclicIndex n hn s 1) = sigma (cyclicIndex n hn s 3) ∧
    applyFourBlockPerm hn h4n sigma s sideSwap
        (cyclicIndex n hn s 2) = sigma (cyclicIndex n hn s 2) ∧
    applyFourBlockPerm hn h4n sigma s sideSwap
        (cyclicIndex n hn s 3) = sigma (cyclicIndex n hn s 1) := by
  constructor
  · simpa using
      (applyFourBlockPerm_apply_local hn h4n sigma s sideSwap (0 : Fin 4))
  constructor
  · simpa using
      (applyFourBlockPerm_apply_local hn h4n sigma s sideSwap (1 : Fin 4))
  constructor
  · simpa using
      (applyFourBlockPerm_apply_local hn h4n sigma s sideSwap (2 : Fin 4))
  · simpa using
      (applyFourBlockPerm_apply_local hn h4n sigma s sideSwap (3 : Fin 4))

/-- The seven local permutation types retained by the current fixed-e
research program. This is a proof-design family, not part of the final
mathematical conjecture. -/
def IsSevenMoveType (pi : Equiv.Perm (Fin 4)) : Prop :=
  pi = swap01 ∨ pi = swap12 ∨ pi = swap23 ∨
  pi = pairShift ∨ pi = canonicalTwist ∨
  pi = endpointSwap ∨ pi = sideSwap

/-- Undirected one-step relation generated by the seven local move types at a
fixed four-block start. The explicit symmetrization is necessary because
canonicalTwist is not an involution. -/
def SevenMoveAt
    {alpha : Type*} {E : Set alpha} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (sigma tau : Fin n ≃ E) (s : Fin n) : Prop :=
  ∃ pi : Equiv.Perm (Fin 4),
    IsSevenMoveType pi ∧
      (tau = applyFourBlockPerm hn h4n sigma s pi ∨
       sigma = applyFourBlockPerm hn h4n tau s pi)

theorem SevenMoveAt.symm
    {alpha : Type*} {E : Set alpha} {n : ℕ}
    {hn : 0 < n} {h4n : 4 ≤ n}
    {sigma tau : Fin n ≃ E} {s : Fin n}
    (h : SevenMoveAt hn h4n sigma tau s) :
    SevenMoveAt hn h4n tau sigma s := by
  rcases h with ⟨pi, hpi, hst | hts⟩
  · exact ⟨pi, hpi, Or.inr hst⟩
  · exact ⟨pi, hpi, Or.inl hts⟩

/-- Every seven-type edge is, in either orientation, an abstract four-block
reorder at the same local start. -/
theorem SevenMoveAt.fourBlockReorder
    {alpha : Type*} {E : Set alpha} {n : ℕ}
    {hn : 0 < n} {h4n : 4 ≤ n}
    {sigma tau : Fin n ≃ E} {s : Fin n}
    (h : SevenMoveAt hn h4n sigma tau s) :
    FourBlockReorder hn sigma tau s := by
  rcases h with ⟨pi, -, hst | hts⟩
  · subst tau
    exact fourBlockReorder_applyFourBlockPerm hn h4n sigma s pi
  · have hrev :
        FourBlockReorder hn tau sigma s := by
      rw [hts]
      exact fourBlockReorder_applyFourBlockPerm hn h4n tau s pi
    exact hrev.symm

end

end Rank4SevenMoveTypes
end HigherRankKUM
