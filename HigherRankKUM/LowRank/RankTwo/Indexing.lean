import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace HigherRankKUM.RankTwo

/-- The first-half index, regarded as an index in `Fin (2*k)`. -/
def firstIndex (k : ℕ) (i : Fin k) : Fin (2 * k) :=
  ⟨i.val, by omega⟩

/-- The second-half index, regarded as an index in `Fin (2*k)`. -/
def secondIndex (k : ℕ) (i : Fin k) : Fin (2 * k) :=
  ⟨k + i.val, by omega⟩

@[simp] theorem firstIndex_val (k : ℕ) (i : Fin k) :
    (firstIndex k i).val = i.val := rfl

@[simp] theorem secondIndex_val (k : ℕ) (i : Fin k) :
    (secondIndex k i).val = k + i.val := rfl

/-- Split a Boolean-labelled copy of `Fin k` into two summands. -/
def boolHalfEquiv (k : ℕ) : Fin k × Bool ≃ Fin k ⊕ Fin k where
  toFun
    | (i, false) => Sum.inl i
    | (i, true) => Sum.inr i
  invFun
    | Sum.inl i => (i, false)
    | Sum.inr i => (i, true)
  left_inv := by rintro ⟨i, b⟩; cases b <;> rfl
  right_inv := by intro s; cases s <;> rfl

/-- The half-weave indexing `0,k,1,k+1,...`. -/
def halfWeaveEquiv (k : ℕ) (_hk : 0 < k) :
    Fin k × Bool ≃ Fin (2 * k) :=
  (boolHalfEquiv k).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[simp] theorem halfWeaveEquiv_false
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    halfWeaveEquiv k hk (i, false) = firstIndex k i := by
  apply Fin.ext
  simp [halfWeaveEquiv, boolHalfEquiv, firstIndex]

@[simp] theorem halfWeaveEquiv_true
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    halfWeaveEquiv k hk (i, true) = secondIndex k i := by
  apply Fin.ext
  simp [halfWeaveEquiv, boolHalfEquiv, secondIndex]
  omega

/-- Cyclic addition by one on `Fin k`. -/
def cyclicSuccEquiv (k : ℕ) (hk : 0 < k) : Fin k ≃ Fin k :=
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  Equiv.addRight 1

def cyclicSucc (k : ℕ) (hk : 0 < k) (i : Fin k) : Fin k :=
  cyclicSuccEquiv k hk i

@[simp] theorem cyclicSucc_val
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    (cyclicSucc k hk i).val = (i.val + 1) % k := by
  simp [cyclicSucc, cyclicSuccEquiv, Fin.add_def]

def lastFin (k : ℕ) (hk : 0 < k) : Fin k := ⟨k - 1, by omega⟩
def zeroFin (k : ℕ) (hk : 0 < k) : Fin k := ⟨0, hk⟩

@[simp] theorem cyclicSucc_last (k : ℕ) (hk : 0 < k) :
    cyclicSucc k hk (lastFin k hk) = zeroFin k hk := by
  apply Fin.ext
  simp [lastFin, zeroFin, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hk)]

/-- Alternate within a pair, then advance cyclically to the next pair. -/
def weaveNext (k : ℕ) (hk : 0 < k) : Fin k × Bool → Fin k × Bool
  | (i, false) => (i, true)
  | (i, true) => (cyclicSucc k hk i, false)

@[simp] theorem weaveNext_false
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    weaveNext k hk (i, false) = (i, true) := rfl

@[simp] theorem weaveNext_true
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    weaveNext k hk (i, true) = (cyclicSucc k hk i, false) := rfl

/-- Transport an arbitrary enumeration through the half weave. -/
def woven {α : Type*} (k : ℕ) (hk : 0 < k)
    (y : Fin (2 * k) ≃ α) : Fin k × Bool ≃ α :=
  (halfWeaveEquiv k hk).trans y

/-- Every woven successor adjacency has one of the two expected forms. -/
theorem woven_successor_adjacency
    {α : Type*} (k : ℕ) (hk : 0 < k)
    (y : Fin (2 * k) ≃ α) (p : Fin k × Bool) :
    (∃ i : Fin k,
        p = (i, false) ∧
        (woven k hk y p, woven k hk y (weaveNext k hk p)) =
          (y (firstIndex k i), y (secondIndex k i))) ∨
    (∃ i : Fin k,
        p = (i, true) ∧
        (woven k hk y p, woven k hk y (weaveNext k hk p)) =
          (y (secondIndex k i), y (firstIndex k (cyclicSucc k hk i)))) := by
  rcases p with ⟨i, b⟩
  cases b
  · left
    exact ⟨i, rfl, by simp [woven]⟩
  · right
    exact ⟨i, rfl, by simp [woven]⟩

end HigherRankKUM.RankTwo
