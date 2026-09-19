import HigherRankKUM.LowRank.RankTwo
import Mathlib.Combinatorics.Matroid.Loop

namespace HigherRankKUM
namespace RankTwoSelection

open Set

noncomputable section

variable {α : Type*}

/-- In a finite loopless rank-two matroid with at least three ground
elements, some element has two distinct basis partners.

This is the elementary selection lemma used by the dangerous-hyperplane
constructions. -/
theorem exists_center_with_two_basis_partners
    (N : Matroid α)
    (hE : N.E.Finite)
    (hRank : N.eRank = (2 : ℕ∞))
    (hCard : 3 ≤ N.E.ncard)
    (hLoopless : N.Loopless) :
    ∃ d p q : α,
      d ≠ p ∧ d ≠ q ∧ p ≠ q ∧
      N.IsBase ({d, p} : Set α) ∧
      N.IsBase ({d, q} : Set α) := by
  letI : N.Loopless := hLoopless
  obtain ⟨B, hB⟩ := N.exists_isBase
  have hBcardE : B.encard = (2 : ℕ∞) := by
    rw [hB.encard_eq_eRank, hRank]
  obtain ⟨u, v, huv, hBpair⟩ := Set.encard_eq_two.mp hBcardE
  have hBfin : B.Finite := hB.indep.finite
  have hBncard : B.ncard = 2 := by
    have h := hBcardE
    rw [← hBfin.cast_ncard_eq] at h
    exact_mod_cast h
  have hBlt : B.ncard < N.E.ncard := by omega
  obtain ⟨w, hwE, hwB⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard hBlt hBfin
  have huE : u ∈ N.E := hB.subset_ground (by rw [hBpair]; simp)
  have hvE : v ∈ N.E := hB.subset_ground (by rw [hBpair]; simp)
  have hwu : w ≠ u := by
    intro h
    subst w
    exact hwB (by rw [hBpair]; simp)
  have hwv : w ≠ v := by
    intro h
    subst w
    exact hwB (by rw [hBpair]; simp)
  have huvInd : N.Indep ({u, v} : Set α) := by
    rw [← hBpair]
    exact hB.indep
  by_cases huw : N.Indep ({u, w} : Set α)
  · refine ⟨u, v, w, huv, hwu.symm, ?_, ?_, ?_⟩
    · exact hwv.symm
    · simpa [hBpair] using hB
    · have hRk : N.eRk ({u, w} : Set α) = (2 : ℕ∞) := by
        rw [huw.eRk_eq_encard, Set.encard_pair hwu.symm]
      exact huw.isBase_of_eRk_ge (by simp) (by rw [hRank, hRk])
  · have huvNonloop : N.IsNonloop u := Matroid.isNonloop_of_loopless huE
    have hvNonloop : N.IsNonloop v := Matroid.isNonloop_of_loopless hvE
    have hwNonloop : N.IsNonloop w := Matroid.isNonloop_of_loopless hwE
    have hvw : N.Indep ({v, w} : Set α) := by
      by_contra hvw
      have hUW :
          N.closure ({u} : Set α) = N.closure ({w} : Set α) :=
        (huvNonloop.closure_eq_closure_iff_eq_or_dep hwNonloop).2
          (Or.inr huw)
      have hVW :
          N.closure ({v} : Set α) = N.closure ({w} : Set α) :=
        (hvNonloop.closure_eq_closure_iff_eq_or_dep hwNonloop).2
          (Or.inr hvw)
      have hUV :
          N.closure ({u} : Set α) = N.closure ({v} : Set α) :=
        hUW.trans hVW.symm
      have hbad :=
        (huvNonloop.closure_eq_closure_iff_eq_or_dep hvNonloop).1 hUV
      rcases hbad with huvEq | hdep
      · exact huv huvEq
      · exact hdep huvInd
    refine ⟨v, u, w, huv.symm, hwv.symm, hwu.symm, ?_, ?_⟩
    · simpa [Set.pair_comm, hBpair] using hB
    · have hRk : N.eRk ({v, w} : Set α) = (2 : ℕ∞) := by
        rw [hvw.eRk_eq_encard, Set.encard_pair hwv.symm]
      exact hvw.isBase_of_eRk_ge (by simp) (by rw [hRank, hRk])

end

end RankTwoSelection
end HigherRankKUM
