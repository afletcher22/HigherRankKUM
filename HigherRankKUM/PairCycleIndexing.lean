import HigherRankKUM.CyclicIndex
import Mathlib.Data.Nat.ModEq

namespace HigherRankKUM
namespace PairCycleIndexing

/-- Successive cyclic offsets add. -/
theorem cyclicIndex_add (n : ℕ) (hn : 0 < n) (i : Fin n) (a b : ℕ) :
    cyclicIndex n hn (cyclicIndex n hn i a) b = cyclicIndex n hn i (a + b) := by
  apply Fin.ext
  simp only [cyclicIndex_val]
  have h := (Nat.mod_modEq (i.val + a) n).add_right b
  simpa [Nat.add_assoc] using h

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

end PairCycleIndexing
end HigherRankKUM
