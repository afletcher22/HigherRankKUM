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



/-- Two loopless rank-two matroids on the same ground set have a common base.

The proof is the parallel-class argument used informally in the `t=1`
dangerous-hyperplane route, stated representation-free. -/
theorem exists_common_base
    (N₁ N₂ : Matroid α)
    (hGround : N₁.E = N₂.E)
    (hRank₁ : N₁.eRank = (2 : ℕ∞))
    (hRank₂ : N₂.eRank = (2 : ℕ∞))
    (hLoopless₁ : N₁.Loopless)
    (hLoopless₂ : N₂.Loopless) :
    ∃ B : Set α, N₁.IsBase B ∧ N₂.IsBase B := by
  letI : N₁.Loopless := hLoopless₁
  letI : N₂.Loopless := hLoopless₂
  by_contra hcommon
  push_neg at hcommon
  obtain ⟨B, hB₁⟩ := N₁.exists_isBase
  have hBcard : B.encard = (2 : ℕ∞) := by
    rw [hB₁.encard_eq_eRank, hRank₁]
  obtain ⟨a, b, hab, hBpair⟩ := Set.encard_eq_two.mp hBcard
  have hAB₁ : N₁.IsBase ({a, b} : Set α) := by
    rwa [← hBpair]
  have haE₁ : a ∈ N₁.E := hAB₁.subset_ground (by simp)
  have hbE₁ : b ∈ N₁.E := hAB₁.subset_ground (by simp)
  have haE₂ : a ∈ N₂.E := by simpa [← hGround] using haE₁
  have hbE₂ : b ∈ N₂.E := by simpa [← hGround] using hbE₁
  have ha₁ : N₁.IsNonloop a := Matroid.isNonloop_of_loopless haE₁
  have hb₁ : N₁.IsNonloop b := Matroid.isNonloop_of_loopless hbE₁
  have ha₂ : N₂.IsNonloop a := Matroid.isNonloop_of_loopless haE₂
  have hb₂ : N₂.IsNonloop b := Matroid.isNonloop_of_loopless hbE₂
  have hAB₂not : ¬ N₂.IsBase ({a, b} : Set α) :=
    hcommon ({a, b} : Set α) hAB₁
  have hAB₂dep : ¬ N₂.Indep ({a, b} : Set α) := by
    intro hI
    apply hAB₂not
    exact hI.isBase_of_eRk_ge (by simp) (by
      rw [hRank₂, hI.eRk_eq_encard, Set.encard_pair hab])
  have hABcl₂ :
      N₂.closure ({a} : Set α) = N₂.closure ({b} : Set α) :=
    (ha₂.closure_eq_closure_iff_eq_or_dep hb₂).2 (Or.inr hAB₂dep)
  have hAll : N₂.E ⊆ N₂.closure ({a} : Set α) := by
    intro x hxE₂
    have hxE₁ : x ∈ N₁.E := by simpa [hGround] using hxE₂
    have hx₁ : N₁.IsNonloop x := Matroid.isNonloop_of_loopless hxE₁
    have hx₂ : N₂.IsNonloop x := Matroid.isNonloop_of_loopless hxE₂
    by_cases hxa : x = a
    · subst x
      exact N₂.mem_closure_self a
    have haxPairNe : a ≠ x := hxa.symm
    by_cases hax₁ : N₁.Indep ({a, x} : Set α)
    · have haxBase₁ : N₁.IsBase ({a, x} : Set α) :=
        hax₁.isBase_of_eRk_ge (by simp) (by
          rw [hRank₁, hax₁.eRk_eq_encard, Set.encard_pair haxPairNe])
      have haxBase₂not : ¬ N₂.IsBase ({a, x} : Set α) :=
        hcommon ({a, x} : Set α) haxBase₁
      have hax₂ : ¬ N₂.Indep ({a, x} : Set α) := by
        intro hI
        apply haxBase₂not
        exact hI.isBase_of_eRk_ge (by simp) (by
          rw [hRank₂, hI.eRk_eq_encard, Set.encard_pair haxPairNe])
      have hcl :
          N₂.closure ({a} : Set α) = N₂.closure ({x} : Set α) :=
        (ha₂.closure_eq_closure_iff_eq_or_dep hx₂).2 (Or.inr hax₂)
      rw [hcl]
      exact N₂.mem_closure_self x
    · have hAXcl₁ :
          N₁.closure ({a} : Set α) = N₁.closure ({x} : Set α) :=
        (ha₁.closure_eq_closure_iff_eq_or_dep hx₁).2 (Or.inr hax₁)
      have hbx₁ : N₁.Indep ({b, x} : Set α) := by
        by_contra hbx₁
        have hBXcl₁ :
            N₁.closure ({b} : Set α) = N₁.closure ({x} : Set α) :=
          (hb₁.closure_eq_closure_iff_eq_or_dep hx₁).2 (Or.inr hbx₁)
        have hABcl₁ :
            N₁.closure ({a} : Set α) = N₁.closure ({b} : Set α) :=
          hAXcl₁.trans hBXcl₁.symm
        rcases (ha₁.closure_eq_closure_iff_eq_or_dep hb₁).1 hABcl₁ with
          habEq | hdep
        · exact hab habEq
        · exact hdep hAB₁.indep
      have hbxNe : b ≠ x := by
        intro h
        subst x
        exact hax₁ (by simpa [Set.pair_comm] using hAB₁.indep)
      have hbxBase₁ : N₁.IsBase ({b, x} : Set α) :=
        hbx₁.isBase_of_eRk_ge (by simp) (by
          rw [hRank₁, hbx₁.eRk_eq_encard, Set.encard_pair hbxNe])
      have hbxBase₂not : ¬ N₂.IsBase ({b, x} : Set α) :=
        hcommon ({b, x} : Set α) hbxBase₁
      have hbx₂ : ¬ N₂.Indep ({b, x} : Set α) := by
        intro hI
        apply hbxBase₂not
        exact hI.isBase_of_eRk_ge (by simp) (by
          rw [hRank₂, hI.eRk_eq_encard, Set.encard_pair hbxNe])
      have hBXcl₂ :
          N₂.closure ({b} : Set α) = N₂.closure ({x} : Set α) :=
        (hb₂.closure_eq_closure_iff_eq_or_dep hx₂).2 (Or.inr hbx₂)
      have hAXcl₂ :
          N₂.closure ({a} : Set α) = N₂.closure ({x} : Set α) :=
        hABcl₂.trans hBXcl₂
      rw [hAXcl₂]
      exact N₂.mem_closure_self x
  have hClosure : N₂.closure ({a} : Set α) = N₂.E :=
    Set.Subset.antisymm (N₂.closure_subset_ground {a}) hAll
  have hr := N₂.eRk_closure_eq ({a} : Set α)
  rw [hClosure, N₂.eRk_ground, hRank₂, ha₂.eRk_eq] at hr
  norm_num at hr

/-- Pair-valued form of `exists_common_base`. -/
theorem exists_common_pair_base
    (N₁ N₂ : Matroid α)
    (hGround : N₁.E = N₂.E)
    (hRank₁ : N₁.eRank = (2 : ℕ∞))
    (hRank₂ : N₂.eRank = (2 : ℕ∞))
    (hLoopless₁ : N₁.Loopless)
    (hLoopless₂ : N₂.Loopless) :
    ∃ a b : α, a ≠ b ∧
      N₁.IsBase ({a, b} : Set α) ∧
      N₂.IsBase ({a, b} : Set α) := by
  obtain ⟨B, hB₁, hB₂⟩ :=
    exists_common_base N₁ N₂ hGround hRank₁ hRank₂ hLoopless₁ hLoopless₂
  have hBcard : B.encard = (2 : ℕ∞) := by
    rw [hB₁.encard_eq_eRank, hRank₁]
  obtain ⟨a, b, hab, rfl⟩ := Set.encard_eq_two.mp hBcard
  exact ⟨a, b, hab, hB₁, hB₂⟩

/-- Two loopless rank-two matroids on the same finite ground set of size at
least three admit a three-element path: the first edge is a basis of `N₁`
and the second edge is a basis of `N₂`.

This is the exact selection statement used in the non-adjacent-good-edge
subcase of the `t=1` dangerous-hyperplane construction. -/
theorem exists_two_matroid_basis_path
    (N₁ N₂ : Matroid α)
    (hGround : N₁.E = N₂.E)
    (hE : N₁.E.Finite)
    (hCard : 3 ≤ N₁.E.ncard)
    (hRank₁ : N₁.eRank = (2 : ℕ∞))
    (hRank₂ : N₂.eRank = (2 : ℕ∞))
    (hLoopless₁ : N₁.Loopless)
    (hLoopless₂ : N₂.Loopless) :
    ∃ c₀ c₁ c₂ : α,
      c₀ ≠ c₁ ∧ c₁ ≠ c₂ ∧ c₀ ≠ c₂ ∧
      N₁.IsBase ({c₀, c₁} : Set α) ∧
      N₂.IsBase ({c₁, c₂} : Set α) := by
  obtain ⟨d, p, q, hdp, hdq, hpq, hdpBase, hdqBase⟩ :=
    exists_center_with_two_basis_partners
      N₁ hE hRank₁ hCard hLoopless₁
  have hdE₁ : d ∈ N₁.E := hdpBase.subset_ground (by simp)
  have hdE₂ : d ∈ N₂.E := by simpa [← hGround] using hdE₁
  letI : N₂.Loopless := hLoopless₂
  have hdNonloop₂ : N₂.IsNonloop d := Matroid.isNonloop_of_loopless hdE₂
  obtain ⟨B, hB, hdB⟩ := hdNonloop₂.exists_mem_isBase
  have hBcard : B.encard = (2 : ℕ∞) := by
    rw [hB.encard_eq_eRank, hRank₂]
  obtain ⟨u, v, huv, hBpair⟩ := Set.encard_eq_two.mp hBcard
  have hdPair : d ∈ ({u, v} : Set α) := by
    rw [← hBpair]
    exact hdB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdPair
  rcases hdPair with hdu | hdv
  · subst u
    have hdv' : d ≠ v := huv
    by_cases hpv : p = v
    · subst p
      refine ⟨q, d, v, hdq.symm, hdv', hpq.symm, ?_, ?_⟩
      · simpa [Set.pair_comm] using hdqBase
      · simpa [hBpair] using hB
    · refine ⟨p, d, v, hdp.symm, hdv', hpv, ?_, ?_⟩
      · simpa [Set.pair_comm] using hdpBase
      · simpa [hBpair] using hB
  · subst v
    have hdu' : d ≠ u := huv.symm
    by_cases hpu : p = u
    · subst p
      refine ⟨q, d, u, hdq.symm, hdu', hpq.symm, ?_, ?_⟩
      · simpa [Set.pair_comm] using hdqBase
      · simpa [Set.pair_comm, hBpair] using hB
    · refine ⟨p, d, u, hdp.symm, hdu', hpu, ?_, ?_⟩
      · simpa [Set.pair_comm] using hdpBase
      · simpa [Set.pair_comm, hBpair] using hB

end

end RankTwoSelection
end HigherRankKUM
