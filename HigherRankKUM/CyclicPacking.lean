import HigherRankKUM.CyclicIndex
import Mathlib.Tactic

namespace HigherRankKUM
namespace CyclicPacking

open scoped BigOperators

noncomputable section

/-- Natural-valued indicator of membership in a finite cyclic subset. -/
def indicator {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℕ :=
  if i ∈ S then 1 else 0

@[simp] theorem sum_indicator {n : ℕ} (S : Finset (Fin n)) :
    (∑ i : Fin n, indicator S i) = S.card := by
  classical
  simp [indicator]

/-- Cyclic translation preserves the sum of any natural-valued function. -/
theorem sum_comp_cyclicIndex
    {n : ℕ} (hn : 0 < n) (a : ℕ) (f : Fin n → ℕ) :
    (∑ i : Fin n, f (cyclicIndex n hn i a)) = ∑ i : Fin n, f i := by
  have hinj :
      Function.Injective (fun i : Fin n => cyclicIndex n hn i a) :=
    cyclicIndex_injective_start n hn a
  have hbij :
      Function.Bijective (fun i : Fin n => cyclicIndex n hn i a) :=
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact Fintype.sum_bijective
    (fun i : Fin n => cyclicIndex n hn i a) hbij _ _ (fun _ => rfl)

/-- If every cyclic length-four interval contains at most three members of
`S`, then `4 |S| ≤ 3n`.

This is the double-counting identity needed to turn the local rank-three-flat
obstruction in a rank-four CBO into a global cardinality bound. -/
theorem four_mul_card_le_three_mul
    {n : ℕ} (hn : 0 < n) (S : Finset (Fin n))
    (hlocal : ∀ i : Fin n,
      indicator S i +
        indicator S (cyclicIndex n hn i 1) +
        indicator S (cyclicIndex n hn i 2) +
        indicator S (cyclicIndex n hn i 3) ≤ 3) :
    4 * S.card ≤ 3 * n := by
  classical
  have hsum :
      (∑ i : Fin n,
        (indicator S i +
          indicator S (cyclicIndex n hn i 1) +
          indicator S (cyclicIndex n hn i 2) +
          indicator S (cyclicIndex n hn i 3))) ≤
        ∑ _i : Fin n, 3 := by
    exact Finset.sum_le_sum (fun i _ => hlocal i)

  have h1 :
      (∑ i : Fin n, indicator S (cyclicIndex n hn i 1)) =
        ∑ i : Fin n, indicator S i :=
    sum_comp_cyclicIndex hn 1 (indicator S)
  have h2 :
      (∑ i : Fin n, indicator S (cyclicIndex n hn i 2)) =
        ∑ i : Fin n, indicator S i :=
    sum_comp_cyclicIndex hn 2 (indicator S)
  have h3 :
      (∑ i : Fin n, indicator S (cyclicIndex n hn i 3)) =
        ∑ i : Fin n, indicator S i :=
    sum_comp_cyclicIndex hn 3 (indicator S)

  simp_rw [Finset.sum_add_distrib] at hsum
  rw [h1, h2, h3, sum_indicator] at hsum
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

/-- Sharp `4k+1` specialization: a cyclic binary word with no four
consecutive ones has at most `3k` ones. -/
theorem card_le_three_mul_of_no_four
    {k : ℕ} {n : ℕ} (hn : 0 < n) (hnk : n = 4 * k + 1)
    (S : Finset (Fin n))
    (hlocal : ∀ i : Fin n,
      indicator S i +
        indicator S (cyclicIndex n hn i 1) +
        indicator S (cyclicIndex n hn i 2) +
        indicator S (cyclicIndex n hn i 3) ≤ 3) :
    S.card ≤ 3 * k := by
  have h := four_mul_card_le_three_mul hn S hlocal
  rw [hnk] at h
  omega

end

end CyclicPacking
end HigherRankKUM
