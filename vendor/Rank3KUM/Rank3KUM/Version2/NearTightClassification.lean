import Rank3KUM.Version2.NearTightGeometry

namespace Rank3KUM.Version2

open Set

variable {α : Type*}

/--
Paper v2, Lemma 8.8.  If `A`, `B`, and `C` are a nonconcurrent triple of
near-tight rank-two flats in a strictly uniformly dense rank-three matroid,
then they exhaust the near-tight family.
-/
theorem nearTight_eq_one_of_nonconcurrent_three
    (M : Matroid α) (k : ℕ)
    (hk : 3 ≤ k)
    (hLoopless : M.Loopless)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDense M k)
    {A B C H : Set α}
    (hAE : A ⊆ M.E)
    (hBE : B ⊆ M.E)
    (hCE : C ⊆ M.E)
    (hHE : H ⊆ M.E)
    (hArank : M.eRk A = 2)
    (hBrank : M.eRk B = 2)
    (hCrank : M.eRk C = 2)
    (hHrank : M.eRk H = 2)
    (hAcard : A.ncard = 2 * k - 1)
    (hBcard : B.ncard = 2 * k - 1)
    (hCcard : C.ncard = 2 * k - 1)
    (hHcard : H.ncard = 2 * k - 1)
    (hAB : A ≠ B)
    (hAC : A ≠ C)
    (hBC : B ≠ C)
    (hABCempty : (A ∩ B) ∩ C = ∅) :
    H = A ∨ H = B ∨ H = C := by
  by_cases hHA : H = A
  · exact Or.inl hHA
  by_cases hHB : H = B
  · exact Or.inr (Or.inl hHB)
  by_cases hHC : H = C
  · exact Or.inr (Or.inr hHC)
  exfalso

  have hAfin : A.Finite := hE.subset hAE
  have hBfin : B.Finite := hE.subset hBE
  have hCfin : C.Finite := hE.subset hCE
  have hHfin : H.Finite := hE.subset hHE
  have hABfin : (A ∩ B).Finite := hAfin.inter_of_left B
  have hACfin : (A ∩ C).Finite := hAfin.inter_of_left C
  have hBCfin : (B ∩ C).Finite := hBfin.inter_of_left C

  obtain ⟨hABcard, hACcard, hBCcard, hUnionCard⟩ :=
    Rank3KUM.pairwise_intersections_ncard_eq_of_three_nearTight
      M k hk hLoopless hE hRank hEcard hStrict
      hAE hBE hCE hArank hBrank hCrank
      hAcard hBcard hCcard hAB hAC hBC hABCempty

  have hEncard : M.E.ncard = 3 * k := by
    have hcast :
        (M.E.ncard : ℕ∞) = ((3 * k : ℕ) : ℕ∞) := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast

  have hUnionSub : A ∪ B ∪ C ⊆ M.E :=
    Set.union_subset (Set.union_subset hAE hBE) hCE
  have hUnionEq : A ∪ B ∪ C = M.E :=
    Set.eq_of_subset_of_ncard_le hUnionSub (by rw [hUnionCard, hEncard]) hE

  have hABACDisjoint : Disjoint (A ∩ B) (A ∩ C) := by
    apply Set.disjoint_left.2
    intro u huAB huAC
    have huABC : u ∈ (A ∩ B) ∩ C := ⟨huAB, huAC.2⟩
    rw [hABCempty] at huABC
    exact huABC
  have hPairUnionBCDisjoint :
      Disjoint ((A ∩ B) ∪ (A ∩ C)) (B ∩ C) := by
    apply Set.disjoint_left.2
    intro u huUnion huBC
    rcases huUnion with huAB | huAC
    · have huABC : u ∈ (A ∩ B) ∩ C := ⟨huAB, huBC.2⟩
      rw [hABCempty] at huABC
      exact huABC
    · have huABC : u ∈ (A ∩ B) ∩ C :=
        ⟨⟨huAC.1, huBC.1⟩, huAC.2⟩
      rw [hABCempty] at huABC
      exact huABC

  let P : Set α := ((A ∩ B) ∪ (A ∩ C)) ∪ (B ∩ C)
  have hPcard : P.ncard = 3 * k - 3 := by
    dsimp [P]
    rw [Set.ncard_union_eq hPairUnionBCDisjoint
          (hABfin.union hACfin) hBCfin,
        Set.ncard_union_eq hABACDisjoint hABfin hACfin,
        hABcard, hACcard, hBCcard]
    omega
  have hPE : P ⊆ M.E := by
    intro u hu
    rcases hu with (huAB | huAC) | huBC
    · exact hAE huAB.1
    · exact hAE huAC.1
    · exact hBE huBC.1
  have hResidualCard : (M.E \ P).ncard = 3 := by
    rw [Set.ncard_sdiff' hPE hE, hEncard, hPcard]
    omega
  have hHDiffSub : H \ P ⊆ M.E \ P := by
    intro u hu
    exact ⟨hHE hu.1, hu.2⟩
  have hHDiffLe : (H \ P).ncard ≤ 3 := by
    rw [← hResidualCard]
    exact Set.ncard_le_ncard hHDiffSub hE.sdiff
  have hHSplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard H P hHfin
  have hHPLower : 2 * k - 4 ≤ (H ∩ P).ncard := by
    rw [hHcard] at hHSplit
    omega

  let HA : Set α := H ∩ A
  let HB : Set α := H ∩ B
  let HC : Set α := H ∩ C
  have hHAfin : HA.Finite := by
    dsimp [HA]
    exact hHfin.inter_of_left A
  have hHBfin : HB.Finite := by
    dsimp [HB]
    exact hHfin.inter_of_left B
  have hHCfin : HC.Finite := by
    dsimp [HC]
    exact hHfin.inter_of_left C
  have hHABfin : (HA ∩ HB).Finite := hHAfin.inter_of_left HB
  have hHACfin : (HA ∩ HC).Finite := hHAfin.inter_of_left HC
  have hHBCfin : (HB ∩ HC).Finite := hHBfin.inter_of_left HC

  have hUnionH : HA ∪ HB ∪ HC = H := by
    apply Set.Subset.antisymm
    · intro u hu
      rcases hu with (huHA | huHB) | huHC
      · exact huHA.1
      · exact huHB.1
      · exact huHC.1
    · intro u huH
      have huE : u ∈ M.E := hHE huH
      have huABC : u ∈ A ∪ B ∪ C := by
        rw [hUnionEq]
        exact huE
      rcases huABC with (huA | huB) | huC
      · exact Or.inl (Or.inl ⟨huH, huA⟩)
      · exact Or.inl (Or.inr ⟨huH, huB⟩)
      · exact Or.inr ⟨huH, huC⟩

  have hHABHACDisjoint : Disjoint (HA ∩ HB) (HA ∩ HC) := by
    apply Set.disjoint_left.2
    intro u huAB' huAC'
    have huABC : u ∈ (A ∩ B) ∩ C := by
      exact ⟨⟨huAB'.1.2, huAB'.2.2⟩, huAC'.2.2⟩
    rw [hABCempty] at huABC
    exact huABC
  have hHPairUnionBCDisjoint :
      Disjoint ((HA ∩ HB) ∪ (HA ∩ HC)) (HB ∩ HC) := by
    apply Set.disjoint_left.2
    intro u huUnion huBC'
    rcases huUnion with huAB' | huAC'
    · have huABC : u ∈ (A ∩ B) ∩ C :=
        ⟨⟨huAB'.1.2, huAB'.2.2⟩, huBC'.2.2⟩
      rw [hABCempty] at huABC
      exact huABC
    · have huABC : u ∈ (A ∩ B) ∩ C :=
        ⟨⟨huAC'.1.2, huBC'.1.2⟩, huAC'.2.2⟩
      rw [hABCempty] at huABC
      exact huABC
  have hHACHBCDisjoint : Disjoint (HA ∩ HC) (HB ∩ HC) := by
    apply Set.disjoint_left.2
    intro u huAC' huBC'
    have huABC : u ∈ (A ∩ B) ∩ C :=
      ⟨⟨huAC'.1.2, huBC'.1.2⟩, huAC'.2.2⟩
    rw [hABCempty] at huABC
    exact huABC

  have hPairUnionEq :
      ((HA ∩ HB) ∪ (HA ∩ HC)) ∪ (HB ∩ HC) = H ∩ P := by
    ext u
    simp only [HA, HB, HC, P, Set.mem_union, Set.mem_inter_iff]
    tauto
  have hPairCard :
      (HA ∩ HB).ncard + (HA ∩ HC).ncard + (HB ∩ HC).ncard =
        (H ∩ P).ncard := by
    rw [← hPairUnionEq,
      Set.ncard_union_eq hHPairUnionBCDisjoint
        (hHABfin.union hHACfin) hHBCfin,
      Set.ncard_union_eq hHABHACDisjoint hHABfin hHACfin]

  have hCrossDistrib :
      (HA ∪ HB) ∩ HC = (HA ∩ HC) ∪ (HB ∩ HC) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  have hCrossCard :
      ((HA ∪ HB) ∩ HC).ncard =
        (HA ∩ HC).ncard + (HB ∩ HC).ncard := by
    rw [hCrossDistrib]
    exact Set.ncard_union_eq hHACHBCDisjoint hHACfin hHBCfin

  have hCountAB :=
    Set.ncard_union_add_ncard_inter HA HB hHAfin hHBfin
  have hCountABC :=
    Set.ncard_union_add_ncard_inter
      (HA ∪ HB) HC (hHAfin.union hHBfin) hHCfin
  rw [hUnionH, hCrossCard] at hCountABC
  have hIncidence :
      HA.ncard + HB.ncard + HC.ncard =
        H.ncard + (H ∩ P).ncard := by
    omega
  have hIncLower :
      4 * k - 5 ≤ HA.ncard + HB.ncard + HC.ncard := by
    rw [hIncidence, hHcard]
    omega

  have hHAle : HA.ncard ≤ k - 1 := by
    dsimp [HA]
    exact
      Rank3KUM.ncard_inter_le_k_sub_one_of_distinct_nearTight
        M k hk hLoopless hE hRank hEcard hStrict
        hHE hAE hHrank hArank hHcard hAcard hHA
  have hHBle : HB.ncard ≤ k - 1 := by
    dsimp [HB]
    exact
      Rank3KUM.ncard_inter_le_k_sub_one_of_distinct_nearTight
        M k hk hLoopless hE hRank hEcard hStrict
        hHE hBE hHrank hBrank hHcard hBcard hHB
  have hHCle : HC.ncard ≤ k - 1 := by
    dsimp [HC]
    exact
      Rank3KUM.ncard_inter_le_k_sub_one_of_distinct_nearTight
        M k hk hLoopless hE hRank hEcard hStrict
        hHE hCE hHrank hCrank hHcard hCcard hHC
  omega

#print axioms Rank3KUM.Version2.nearTight_eq_one_of_nonconcurrent_three

end Rank3KUM.Version2
