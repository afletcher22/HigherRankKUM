import HigherRankKUM.Rank4.T0SaturatedCap
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4SaturatedFourWindowDefect

open Set
open scoped BigOperators

noncomputable section

/-- Number of marked positions among the four cyclic positions starting at i. -/
noncomputable def fourHitCount
    {n : ℕ} (hn : 0 < n) (Good : Fin n → Prop) (i : Fin n) : ℕ := by
  classical
  exact ∑ q : Fin 4, if Good (cyclicIndex n hn i q.val) then 1 else 0

/-- Starts whose four-window contains at least two marked positions. -/
def multiHitStarts
    {n : ℕ} (hn : 0 < n) (Good : Fin n → Prop) : Set (Fin n) :=
  {i | 2 ≤ fourHitCount hn Good i}

/-- Cyclic translation by a fixed offset is a permutation of Fin n. -/
noncomputable def cyclicShiftEquiv
    (n : ℕ) (hn : 0 < n) (t : ℕ) : Fin n ≃ Fin n :=
  Equiv.ofBijective
    (fun i : Fin n => cyclicIndex n hn i t)
    ⟨cyclicIndex_injective_start n hn t,
      Finite.injective_iff_surjective.mp
        (cyclicIndex_injective_start n hn t)⟩

/-- Double-counting identity: summing the number of marked positions over all
cyclic four-windows counts every marked position exactly four times. -/
theorem sum_fourHitCount_eq_four_mul_ncard
    {n : ℕ} (hn : 0 < n) (Good : Fin n → Prop) :
    (∑ i : Fin n, fourHitCount hn Good i) =
      4 * ({i | Good i} : Set (Fin n)).ncard := by
  classical
  have hshift (q : Fin 4) :
      (∑ i : Fin n,
        if Good (cyclicIndex n hn i q.val) then 1 else 0) =
      (∑ i : Fin n, if Good i then 1 else 0) := by
    have hinj :
        Function.Injective (fun i : Fin n => cyclicIndex n hn i q.val) :=
      cyclicIndex_injective_start n hn q.val
    have hbij :
        Function.Bijective (fun i : Fin n => cyclicIndex n hn i q.val) :=
      ⟨hinj, Finite.surjective_of_injective hinj⟩
    exact hbij.sum_comp
      (fun j : Fin n => if Good j then (1 : ℕ) else 0)
  have hbase :
      (∑ i : Fin n, if Good i then 1 else 0) =
        ({i | Good i} : Set (Fin n)).ncard := by
    simpa only [Finset.sum_boole, Set.fintypeCard_eq_ncard]
  unfold fourHitCount
  rw [Finset.sum_comm]
  calc
    (∑ q : Fin 4, ∑ i : Fin n,
      if Good (cyclicIndex n hn i q.val) then 1 else 0)
        = ∑ q : Fin 4, ({i | Good i} : Set (Fin n)).ncard := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [hshift q, hbase]
    _ = 4 * ({i | Good i} : Set (Fin n)).ncard := by
      simp [Nat.mul_comm]

/-- Constant-defect theorem for saturated four-window hitting.

On a cycle of length 4k+1, suppose exactly k+2 positions are marked and every
four consecutive positions contain a mark. Then at most seven starts have two
or more marked positions in their four-window.

The number seven is independent of k: total mark-window incidences are
4(k+2)=4k+8, while the 4k+1 windows each require one incidence. -/
theorem multiHitStarts_ncard_le_seven
    {k : ℕ}
    (Good : Fin (4 * k + 1) → Prop)
    (hGoodCard :
      ({i | Good i} : Set (Fin (4 * k + 1))).ncard = k + 2)
    (hHit :
      ∀ i : Fin (4 * k + 1),
        Good i ∨
        Good (cyclicIndex (4 * k + 1) (by omega) i 1) ∨
        Good (cyclicIndex (4 * k + 1) (by omega) i 2) ∨
        Good (cyclicIndex (4 * k + 1) (by omega) i 3)) :
    (multiHitStarts (by omega) Good).ncard ≤ 7 := by
  classical
  let n := 4 * k + 1
  let hn : 0 < n := by
    dsimp [n]
    omega
  let B : Set (Fin n) := multiHitStarts hn Good
  have hcount_ge_one : ∀ i : Fin n, 1 ≤ fourHitCount hn Good i := by
    intro i
    have hone (q : Fin 4)
        (hq : Good (cyclicIndex n hn i q.val)) :
        1 ≤ fourHitCount hn Good i := by
      unfold fourHitCount
      calc
        1 = (if Good (cyclicIndex n hn i q.val) then 1 else 0) := by
          simp [hq]
        _ ≤ ∑ r : Fin 4,
            if Good (cyclicIndex n hn i r.val) then 1 else 0 := by
          exact Finset.single_le_sum
            (fun r _ => Nat.zero_le
              (if Good (cyclicIndex n hn i r.val) then 1 else 0))
            (Finset.mem_univ q)
    have hi := hHit i
    rcases hi with h0 | h1 | h2 | h3
    · exact hone 0 (by simpa [n, cyclicIndex_zero] using h0)
    · exact hone 1 (by simpa [n] using h1)
    · exact hone 2 (by simpa [n] using h2)
    · exact hone 3 (by simpa [n] using h3)
  have hpoint :
      ∀ i : Fin n,
        1 + (if i ∈ B then 1 else 0) ≤ fourHitCount hn Good i := by
    intro i
    by_cases hiB : i ∈ B
    · simp only [hiB, if_true]
      dsimp [B, multiHitStarts] at hiB
      omega
    · simp only [hiB, if_false, Nat.add_zero]
      exact hcount_ge_one i
  have hsum_le :
      (∑ i : Fin n, (1 + (if i ∈ B then 1 else 0))) ≤
        ∑ i : Fin n, fourHitCount hn Good i := by
    exact Finset.sum_le_sum (fun i _ => hpoint i)
  have hBsum :
      (∑ i : Fin n, if i ∈ B then 1 else 0) = B.ncard := by
    simpa only [Finset.sum_boole, Set.fintypeCard_eq_ncard]
  have hleft :
      (∑ i : Fin n, (1 + (if i ∈ B then 1 else 0))) =
        n + B.ncard := by
    rw [Finset.sum_add_distrib, hBsum]
    simp [n]
  have htotal :
      (∑ i : Fin n, fourHitCount hn Good i) = 4 * (k + 2) := by
    have h :=
      sum_fourHitCount_eq_four_mul_ncard hn Good
    rw [hGoodCard] at h
    simpa [n] using h
  rw [hleft, htotal] at hsum_le
  dsimp [n, B] at hsum_le ⊢
  omega

end

end Rank4SaturatedFourWindowDefect
end HigherRankKUM
