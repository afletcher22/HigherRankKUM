import Rank3KUM.CyclicOrder

namespace Rank3KUM

open Set

variable {α : Type*}

/-- Rotate an enumeration one cyclic position to the left. -/
noncomputable def rotateOneOrder
    {E : Set α} {m : ℕ}
    (hm : 0 < m) (small : Fin m ≃ E) :
    Fin m ≃ E :=
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  (Equiv.addRight 1).trans small

@[simp] theorem rotateOneOrder_apply
    {E : Set α} {m : ℕ}
    (hm : 0 < m) (small : Fin m ≃ E)
    (i : Fin m) :
    ((rotateOneOrder hm small i : E) : α) =
      (small (cyclicIndex m hm i 1) : α) := by
  simp [rotateOneOrder, cyclicIndex, Fin.add_def]

/-- Cyclic offsets associate. -/
theorem cyclicIndex_cyclicIndex
    (n : ℕ) (hn : 0 < n) (i : Fin n) (a b : ℕ) :
    cyclicIndex n hn (cyclicIndex n hn i a) b =
      cyclicIndex n hn i (a + b) := by
  apply Fin.ext
  simp only [cyclicIndex_val]
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Rotating a cyclic basis order preserves the cyclic basis property. -/
theorem CyclicBasisOrder3.rotateOne
    (M : Matroid α) {E : Set α} {m : ℕ}
    (hm : 0 < m) (small : Fin m ≃ E)
    (hsmall : CyclicBasisOrder3 M hm small) :
    CyclicBasisOrder3 M hm (rotateOneOrder hm small) := by
  intro i
  have hs := hsmall (cyclicIndex m hm i 1)
  have h₁ :
      cyclicIndex m hm (cyclicIndex m hm i 1) 1 =
        cyclicIndex m hm i 2 := by
    simpa using cyclicIndex_cyclicIndex m hm i 1 1
  have h₂ :
      cyclicIndex m hm (cyclicIndex m hm i 1) 2 =
        cyclicIndex m hm i 3 := by
    simpa using cyclicIndex_cyclicIndex m hm i 1 2
  have h₃ :
      cyclicIndex m hm (cyclicIndex m hm i 2) 1 =
        cyclicIndex m hm i 3 := by
    simpa using cyclicIndex_cyclicIndex m hm i 2 1
  rw [rotateOneOrder_apply, rotateOneOrder_apply,
    rotateOneOrder_apply, h₁, h₃]
  rw [h₁, h₂] at hs
  exact hs

end Rank3KUM
