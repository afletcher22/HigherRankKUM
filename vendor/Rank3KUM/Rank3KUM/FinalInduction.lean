import Rank3KUM.FinalReduction
import Rank3KUM.NearTightGeometry
import Rank3KUM.SmallCases
import Rank3KUM.Version2.SixPointMatroidBridge

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
Strong induction completes the theorem from the single remaining
six-element input.  The strict cases with `k ≥ 3` now obtain their
near-tight hitting basis automatically.
-/
theorem rankThreeKUM_of_small_two_and_strict_deletion
    (hTwo :
      ∀ N : Matroid α,
        N.E.Finite →
        N.eRank = 3 →
        N.E.encard = (6 : ℕ∞) →
        UniformlyDense N 2 →
        ∃ order : Fin 6 ≃ N.E,
          CyclicBasisOrder3 N (by omega) order) :
    ∀ (k : ℕ) (M : Matroid α) (_hk : 0 < k),
      M.E.Finite →
      M.eRank = 3 →
      M.E.encard = ((3 * k : ℕ) : ℕ∞) →
      UniformlyDense M k →
      ∃ order : Fin (3 * k) ≃ M.E,
        CyclicBasisOrder3 M (by omega) order := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro M hk hE hRank hEcard hDense
      by_cases hkOne : k = 1
      · subst k
        simpa using
          exists_cyclicBasisOrder3_of_ground_encard_three
            M hE hRank (by simpa using hEcard)
      by_cases hkTwo : k = 2
      · subst k
        simpa using
          hTwo M hE hRank (by simpa using hEcard) hDense
      have hkThree : 3 ≤ k := by omega
      apply
        exists_cyclicBasisOrder3_of_strict_case
          M k hk hE hRank hEcard hDense
      intro hStrict
      have hLoopless : M.Loopless :=
        loopless_of_uniformlyDense M k hk hDense
      obtain ⟨D, hD, hHits⟩ :=
        exists_isBase_hitsNearTight_of_strict_rankThree
          M k hkThree hLoopless hE hRank hEcard hStrict
      have hDelCard :
          (Matroid.delete M D).E.encard =
            ((3 * (k - 1) : ℕ) : ℕ∞) :=
        delete_ground_encard_eq_three_mul_pred
          M k hk hRank hEcard hD
      have hComplementCard :
          (M.E \ D).encard =
            ((3 * (k - 1) : ℕ) : ℕ∞) := by
        simpa using hDelCard
      have hDelRank :
          (Matroid.delete M D).eRank = 3 :=
        eRank_delete_eq_three_of_strict
          M k hkThree hRank hStrict hD
          hComplementCard
      have hDelDense :
          UniformlyDense (Matroid.delete M D) (k - 1) :=
        uniformlyDense_delete_of_strict_of_hitsNearTight
          M k hk hE hRank hDense hStrict hD
          hComplementCard hHits
      have hDelFinite :
          (Matroid.delete M D).E.Finite := by
        rw [Matroid.delete_ground]
        exact hE.subset Set.sdiff_subset
      obtain ⟨small, hsmall⟩ :=
        ih (k - 1) (by omega)
          (Matroid.delete M D) (by omega)
          hDelFinite hDelRank hDelCard hDelDense
      exact
        exists_cyclicBasisOrder3_of_cyclic_basis_deletion
          M k hkThree hRank hD hDelRank
          small hsmall

/-- The complete rank-three cyclic ordering theorem. -/
theorem rankThreeKUM
    (k : ℕ) (M : Matroid α) (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  apply
    rankThreeKUM_of_small_two_and_strict_deletion
      (fun N hNE hNRank hNCard hNDense =>
        Version2.exists_cyclicBasisOrder3_of_ground_encard_six_structural
          N hNE hNRank hNCard hNDense)
      k M hk hE hRank hEcard hDense

#print axioms Rank3KUM.rankThreeKUM

#print axioms Rank3KUM.rankThreeKUM_of_small_two_and_strict_deletion

end

end Rank3KUM