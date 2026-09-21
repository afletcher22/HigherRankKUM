import Rank3KUM.CyclicOrder

namespace Rank3KUM

open Set

variable {α : Type*}

/-- Append a three-element basis at the wraparound gap of a cyclic basis order. -/
theorem cyclicBasisOrder3_appendBlock_wrap
    (M : Matroid α) {E D : Set α} {m : ℕ}
    (hm : 2 ≤ m)
    (hED : Disjoint E D)
    (small : Fin m ≃ E)
    (block : Fin 3 ≃ D)
    (hsmall : CyclicBasisOrder3 M (by omega) small)
    (hD : M.IsBase D)
    (hleft₁ :
      M.IsBase
        ({(small ⟨m - 2, by omega⟩ : α),
          (small ⟨m - 1, by omega⟩ : α),
          (block 0 : α)} : Set α))
    (hleft₂ :
      M.IsBase
        ({(small ⟨m - 1, by omega⟩ : α),
          (block 0 : α),
          (block 1 : α)} : Set α))
    (hright₁ :
      M.IsBase
        ({(block 1 : α),
          (block 2 : α),
          (small ⟨0, by omega⟩ : α)} : Set α))
    (hright₂ :
      M.IsBase
        ({(block 2 : α),
          (small ⟨0, by omega⟩ : α),
          (small ⟨1, by omega⟩ : α)} : Set α)) :
    CyclicBasisOrder3 M (by omega)
      (appendBlockOrder hED small block) := by
  intro i
  refine Fin.addCases (m := m) (n := 3) ?_ ?_ i
  · intro j
    by_cases hj : j.val + 2 < m
    · let j₁ : Fin m := ⟨j.val + 1, by omega⟩
      let j₂ : Fin m := ⟨j.val + 2, by omega⟩
      have hnew₁ :
          cyclicIndex (m + 3) (by omega)
              (Fin.castAdd 3 j) 1 =
            Fin.castAdd 3 j₁ := by
        apply Fin.ext
        change (j.val + 1) % (m + 3) = j.val + 1
        rw [Nat.mod_eq_of_lt (by omega)]
      have hnew₂ :
          cyclicIndex (m + 3) (by omega)
              (Fin.castAdd 3 j) 2 =
            Fin.castAdd 3 j₂ := by
        apply Fin.ext
        change (j.val + 2) % (m + 3) = j.val + 2
        rw [Nat.mod_eq_of_lt (by omega)]
      have hold₁ :
          cyclicIndex m (by omega) j 1 = j₁ := by
        apply Fin.ext
        change (j.val + 1) % m = j.val + 1
        rw [Nat.mod_eq_of_lt (by omega)]
      have hold₂ :
          cyclicIndex m (by omega) j 2 = j₂ := by
        apply Fin.ext
        change (j.val + 2) % m = j.val + 2
        rw [Nat.mod_eq_of_lt hj]
      have hs := hsmall j
      rw [hold₁, hold₂] at hs
      rw [hnew₁, hnew₂,
        appendBlockOrder_old, appendBlockOrder_old,
        appendBlockOrder_old]
      exact hs
    · have hjcase : j.val = m - 2 ∨ j.val = m - 1 := by
        omega
      rcases hjcase with hjlast₂ | hjlast
      · have hjEq : j = (⟨m - 2, by omega⟩ : Fin m) := by
          apply Fin.ext
          exact hjlast₂
        have hnew₁ :
            cyclicIndex (m + 3) (by omega)
                (Fin.castAdd 3 (⟨m - 2, by omega⟩ : Fin m)) 1 =
              Fin.castAdd 3 (⟨m - 1, by omega⟩ : Fin m) := by
          apply Fin.ext
          change (m - 2 + 1) % (m + 3) = m - 1
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        have hnew₂ :
            cyclicIndex (m + 3) (by omega)
                (Fin.castAdd 3 (⟨m - 2, by omega⟩ : Fin m)) 2 =
              Fin.natAdd m (0 : Fin 3) := by
          apply Fin.ext
          change (m - 2 + 2) % (m + 3) = m
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hjEq, hnew₁, hnew₂,
          appendBlockOrder_old, appendBlockOrder_old,
          appendBlockOrder_block]
        exact hleft₁
      · have hjEq : j = (⟨m - 1, by omega⟩ : Fin m) := by
          apply Fin.ext
          exact hjlast
        have hnew₁ :
            cyclicIndex (m + 3) (by omega)
                (Fin.castAdd 3 (⟨m - 1, by omega⟩ : Fin m)) 1 =
              Fin.natAdd m (0 : Fin 3) := by
          apply Fin.ext
          change (m - 1 + 1) % (m + 3) = m
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        have hnew₂ :
            cyclicIndex (m + 3) (by omega)
                (Fin.castAdd 3 (⟨m - 1, by omega⟩ : Fin m)) 2 =
              Fin.natAdd m (1 : Fin 3) := by
          apply Fin.ext
          change (m - 1 + 2) % (m + 3) = m + 1
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hjEq, hnew₁, hnew₂,
          appendBlockOrder_old, appendBlockOrder_block,
          appendBlockOrder_block]
        exact hleft₂
  · intro j
    have hj :
        j = (0 : Fin 3) ∨ j = (1 : Fin 3) ∨ j = (2 : Fin 3) := by
      fin_cases j
      · left
        apply Fin.ext
        rfl
      · right
        left
        apply Fin.ext
        rfl
      · right
        right
        apply Fin.ext
        rfl
    rcases hj with rfl | rfl | rfl
    · have hnew₁ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (0 : Fin 3)) 1 =
            Fin.natAdd m (1 : Fin 3) := by
        apply Fin.ext
        change (m + 0 + 1) % (m + 3) = m + 1
        rw [Nat.mod_eq_of_lt (by omega)]
      have hnew₂ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (0 : Fin 3)) 2 =
            Fin.natAdd m (2 : Fin 3) := by
        apply Fin.ext
        change (m + 0 + 2) % (m + 3) = m + 2
        rw [Nat.mod_eq_of_lt (by omega)]
      have hDb :
          M.IsBase
            ({(block 0 : α), (block 1 : α), (block 2 : α)} : Set α) := by
        rw [← TwoGap.set_eq_triple_of_fin3_equiv block]
        exact hD
      rw [hnew₁, hnew₂,
        appendBlockOrder_block, appendBlockOrder_block,
        appendBlockOrder_block]
      exact hDb
    · have hnew₁ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (1 : Fin 3)) 1 =
            Fin.natAdd m (2 : Fin 3) := by
        apply Fin.ext
        change (m + 1 + 1) % (m + 3) = m + 2
        rw [Nat.mod_eq_of_lt (by omega)]
      have hnew₂ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (1 : Fin 3)) 2 =
            Fin.castAdd 3 (⟨0, by omega⟩ : Fin m) := by
        apply Fin.ext
        change (m + 1 + 2) % (m + 3) = 0
        rw [show m + 1 + 2 = m + 3 by omega, Nat.mod_self]
      rw [hnew₁, hnew₂,
        appendBlockOrder_block, appendBlockOrder_block,
        appendBlockOrder_old]
      exact hright₁
    · have hnew₁ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (2 : Fin 3)) 1 =
            Fin.castAdd 3 (⟨0, by omega⟩ : Fin m) := by
        apply Fin.ext
        change (m + 2 + 1) % (m + 3) = 0
        rw [show m + 2 + 1 = m + 3 by omega, Nat.mod_self]
      have hnew₂ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (2 : Fin 3)) 2 =
            Fin.castAdd 3 (⟨1, by omega⟩ : Fin m) := by
        apply Fin.ext
        change (m + 2 + 2) % (m + 3) = 1
        rw [show m + 2 + 2 = (m + 3) + 1 by omega]
        simp [Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
      rw [hnew₁, hnew₂,
        appendBlockOrder_block, appendBlockOrder_old,
        appendBlockOrder_old]
      exact hright₂

end Rank3KUM
