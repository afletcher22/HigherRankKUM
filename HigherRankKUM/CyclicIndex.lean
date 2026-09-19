import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq

namespace HigherRankKUM

noncomputable section

/-- Add a natural offset to a finite cyclic index. -/
def cyclicIndex (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ) : Fin n :=
  ⟨(i.val + j) % n, Nat.mod_lt _ hn⟩

@[simp] theorem cyclicIndex_val
    (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ) :
    (cyclicIndex n hn i j).val = (i.val + j) % n := by
  rfl

@[simp] theorem cyclicIndex_zero
    (n : ℕ) (hn : 0 < n) (i : Fin n) :
    cyclicIndex n hn i 0 = i := by
  apply Fin.ext
  simp [cyclicIndex, Nat.mod_eq_of_lt i.isLt]

/-- Successive cyclic shifts compose by adding their offsets. -/
theorem cyclicIndex_add
    (n : ℕ) (hn : 0 < n) (i : Fin n) (a b : ℕ) :
    cyclicIndex n hn (cyclicIndex n hn i a) b =
      cyclicIndex n hn i (a + b) := by
  apply Fin.ext
  simp only [cyclicIndex_val]
  have h := (Nat.mod_modEq (i.val + a) n).add_right b
  simpa [Nat.add_assoc] using h

/-- For a fixed offset, cyclic translation is injective in the starting index. -/
theorem cyclicIndex_injective_start
    (n : ℕ) (hn : 0 < n) (a : ℕ) :
    Function.Injective (fun i : Fin n => cyclicIndex n hn i a) := by
  intro i j hEq
  apply Fin.ext
  have hmod : i.val + a ≡ j.val + a [MOD n] := by
    change (i.val + a) % n = (j.val + a) % n
    exact congrArg Fin.val hEq
  exact (Nat.ModEq.add_right_cancel' a hmod).eq_of_lt_of_lt i.isLt j.isLt

/-- From a common cyclic start, offsets smaller than the modulus are injective. -/
theorem cyclicIndex_injective_offsets
    (n : ℕ) (hn : 0 < n) (i : Fin n) {a b : ℕ}
    (ha : a < n) (hb : b < n)
    (hEq : cyclicIndex n hn i a = cyclicIndex n hn i b) : a = b := by
  have hmod : i.val + a ≡ i.val + b [MOD n] := by
    change (i.val + a) % n = (i.val + b) % n
    exact congrArg Fin.val hEq
  exact (Nat.ModEq.add_left_cancel' i.val hmod).eq_of_lt_of_lt ha hb

/-- A nonzero offset smaller than the cycle length does not return to its start. -/
theorem cyclicIndex_ne_self_of_pos_of_lt
    (n : ℕ) (hn : 0 < n) (i : Fin n) {a : ℕ}
    (ha0 : 0 < a) (haN : a < n) :
    cyclicIndex n hn i a ≠ i := by
  intro h
  have h' : cyclicIndex n hn i a = cyclicIndex n hn i 0 := by simpa using h
  have : a = 0 := cyclicIndex_injective_offsets n hn i haN hn h'
  omega

/-- Every cyclic position has a unique relative offset from a fixed start. -/
theorem existsUnique_cyclicIndex_offset
    (n : ℕ) (hn : 0 < n) (i q : Fin n) :
    ∃! t : Fin n, q = cyclicIndex n hn i t.val := by
  have hbij : Function.Bijective (fun t : Fin n => cyclicIndex n hn i t.val) := by
    exact (Finite.bijective_iff_injective_and_card _ _).2
      ⟨by
        intro a b h
        apply Fin.ext
        exact cyclicIndex_injective_offsets n hn i a.isLt b.isLt h,
       by simp⟩
  obtain ⟨t, ht⟩ := hbij.2 q
  refine ⟨t, ht.symm, ?_⟩
  intro u hu
  exact hbij.1 (hu.symm.trans ht)

end

end HigherRankKUM
