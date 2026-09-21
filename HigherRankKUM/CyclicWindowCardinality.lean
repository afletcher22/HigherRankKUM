import HigherRankKUM.CyclicOrder
import Mathlib.Data.Set.Card

namespace HigherRankKUM

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- A cyclic window has exactly its nominal number of elements whenever its
length does not exceed the ambient cycle length.

The defining map from `Fin r` is injective because cyclic offsets below
`n` are distinct and the cyclic enumeration itself is an equivalence. -/
theorem cyclicWindow_ncard_eq
    {E : Set α} {n r : ℕ}
    (hn : 0 < n) (hrn : r ≤ n)
    (σ : Fin n ≃ E) (i : Fin n) :
    (cyclicWindow r hn σ i).ncard = r := by
  have hinj :
      Function.Injective
        (fun j : Fin r =>
          (σ (cyclicIndex n hn i j.val) : α)) := by
    intro a b hab
    apply Fin.ext
    have hidx :
        cyclicIndex n hn i a.val =
          cyclicIndex n hn i b.val := by
      apply σ.injective
      apply Subtype.ext
      exact hab
    exact cyclicIndex_injective_offsets n hn i
      (lt_of_lt_of_le a.isLt hrn)
      (lt_of_lt_of_le b.isLt hrn)
      hidx
  calc
    (cyclicWindow r hn σ i).ncard
        = Nat.card (Fin r) := by
            simpa [cyclicWindow] using
              (Set.ncard_range_of_injective hinj)
    _ = r := by simp

/-- Every cyclic window is contained in the target set enumerated by the
cyclic order. -/
theorem cyclicWindow_subset_target
    {E : Set α} {n r : ℕ}
    (hn : 0 < n)
    (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow r hn σ i ⊆ E := by
  rintro x ⟨j, rfl⟩
  exact (σ _).property

/-- In a rank-four matroid, a four-element cyclic window contained in the
ground set is either a base or dependent.  Consequently, a non-base such
window is dependent. -/
theorem cyclicWindow_four_dep_of_not_isBase
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (hEsub : E ⊆ M.E)
    (hRank : M.eRank = (4 : ℕ∞))
    (σ : Fin n ≃ E) (i : Fin n)
    (hnot : ¬ M.IsBase (cyclicWindow 4 hn σ i)) :
    M.Dep (cyclicWindow 4 hn σ i) := by
  have hground :
      cyclicWindow 4 hn σ i ⊆ M.E :=
    (cyclicWindow_subset_target hn σ i).trans hEsub
  apply dep_of_not_indep ?_ hground
  intro hI
  apply hnot
  have hfin : (cyclicWindow 4 hn σ i).Finite :=
    Set.toFinite _
  apply hI.isBase_of_eRk_ge hfin
  have henc :
      (cyclicWindow 4 hn σ i).encard = (4 : ℕ∞) := by
    rw [← hfin.cast_ncard_eq, cyclicWindow_ncard_eq hn h4n σ i]
  rw [hRank, hI.eRk_eq_encard, henc]

end

end HigherRankKUM
