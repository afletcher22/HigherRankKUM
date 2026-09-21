import Rank3KUM.Version2.NearTightClassification

namespace Rank3KUM.Version2

open Set

variable {α : Type*}

/--
Paper v2, Proposition 8.11.  This has the same conclusion as the legacy
compiled theorem, but in the nonconcurrent branch it uses the strengthened
Lemma 8.8 directly: the three near-tight flats are the entire near-tight
family, so the basis chosen from their pairwise intersections hits every one.
-/
theorem exists_isBase_hitsNearTight_of_strict_rankThree
    (M : Matroid α) (k : ℕ)
    (hk : 3 ≤ k)
    (hLoopless : M.Loopless)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDense M k) :
    ∃ D : Set α,
      M.IsBase D ∧ HitsNearTightRankTwo M k D := by
  by_cases hExists :
      ∃ A : Set α, A ⊆ M.E ∧
        M.eRk A = 2 ∧
        A.ncard = 2 * k - 1
  · by_cases hCommon :
        ∃ e : α, e ∈ M.E ∧
          ∀ A : Set α, A ⊆ M.E →
            M.eRk A = 2 →
            A.ncard = 2 * k - 1 →
            e ∈ A
    · exact
        Rank3KUM.exists_isBase_hitsNearTight_of_common_point
          M k hLoopless hCommon
    · obtain ⟨A, B, C, hA, hB, hC,
          hAB, hAC, hBC, hABCempty⟩ :=
        Rank3KUM.exists_nonconcurrent_three_nearTight
          M k hk hLoopless hE hRank hEcard
          hStrict hExists hCommon
      rcases hA with ⟨hAE, hArank, hAcard⟩
      rcases hB with ⟨hBE, hBrank, hBcard⟩
      rcases hC with ⟨hCE, hCrank, hCcard⟩
      have hAflat : M.IsFlat A :=
        Rank3KUM.isFlat_of_strict_rankTwo_ncard_eq
          M k hE hRank hStrict hAE hArank hAcard
      have hBflat : M.IsFlat B :=
        Rank3KUM.isFlat_of_strict_rankTwo_ncard_eq
          M k hE hRank hStrict hBE hBrank hBcard
      have hCflat : M.IsFlat C :=
        Rank3KUM.isFlat_of_strict_rankTwo_ncard_eq
          M k hE hRank hStrict hCE hCrank hCcard
      have hABnonempty : (A ∩ B).Nonempty :=
        Rank3KUM.inter_nonempty_of_nearTight
          M k hk hE hEcard hAE hBE hAcard hBcard
      have hACnonempty : (A ∩ C).Nonempty :=
        Rank3KUM.inter_nonempty_of_nearTight
          M k hk hE hEcard hAE hCE hAcard hCcard
      have hBCnonempty : (B ∩ C).Nonempty :=
        Rank3KUM.inter_nonempty_of_nearTight
          M k hk hE hEcard hBE hCE hBcard hCcard
      obtain ⟨x, hx, y, hy, z, hz, hD⟩ :=
        Rank3KUM.exists_isBase_of_pairwise_intersections_three_flats
          M hLoopless hRank hAflat hBflat hCflat
          hABnonempty hACnonempty hBCnonempty hABCempty
      refine ⟨({x, y, z} : Set α), hD, ?_⟩
      intro H hHE hHrank hHcard
      obtain hEq | hEq | hEq :=
        nearTight_eq_one_of_nonconcurrent_three
          M k hk hLoopless hE hRank hEcard hStrict
          hAE hBE hCE hHE
          hArank hBrank hCrank hHrank
          hAcard hBcard hCcard hHcard
          hAB hAC hBC hABCempty
      · subst H
        exact ⟨x, hx.1, by simp⟩
      · subst H
        exact ⟨x, hx.2, by simp⟩
      · subst H
        exact ⟨y, hy.2, by simp⟩
  · exact
      Rank3KUM.exists_isBase_hitsNearTight_of_no_nearTight
        M k hExists

#print axioms Rank3KUM.Version2.exists_isBase_hitsNearTight_of_strict_rankThree

end Rank3KUM.Version2
