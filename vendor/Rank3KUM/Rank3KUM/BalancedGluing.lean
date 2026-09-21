import Rank3KUM.TightFlatAutomatic
import Rank3KUM.ContractInterleave

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
Common rank-three gluing interface for a `k`-point side and a `2k`-element
pair side. The only matroid-specific input is that every point lifts each
within-block and across-block adjacent pair to a basis.
-/
theorem exists_cyclicBasisOrder3_of_point_pair_gluing_clean
    (M : Matroid α) {P Q : Set α} {k : ℕ}
    (hk : 0 < k)
    (hPQ : Disjoint P Q)
    (hUnion : P ∪ Q = M.E)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ Q)
    (hwithin : ∀ (i j : Fin k),
      M.IsBase
        ({(points j : α),
          (pairs (i, false) : α),
          (pairs (i, true) : α)} : Set α))
    (hacross : ∀ (i j : Fin k),
      M.IsBase
        ({(points j : α),
          (pairs (i, true) : α),
          (pairs (cyclicIndex k hk i 1, false) : α)} : Set α)) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  let localOrder : Fin (3 * k) ≃ (P ∪ Q : Set α) :=
    interleaveOneTwo hPQ points pairs
  have hLocal : CyclicBasisOrder3 M (by omega) localOrder := by
    apply cyclicBasisOrder3_interleaveOneTwo M hk hPQ points pairs
    · intro i
      exact hwithin i i
    · intro i
      have h := hwithin i (cyclicIndex k hk i 1)
      convert h using 1
      ext x
      simp [or_comm, or_left_comm]
    · intro i
      have h := hacross i (cyclicIndex k hk i 1)
      convert h using 1
      ext x
      simp [or_comm, or_left_comm]
  let order : Fin (3 * k) ≃ M.E :=
    localOrder.trans (Equiv.setCongr hUnion)
  refine ⟨order, ?_⟩
  intro i
  have hi := hLocal i
  simpa only [order, localOrder, Equiv.trans_apply,
    Equiv.setCongr_apply] using hi

/-- The contraction ground is definitionally the complement of the contracted set. -/
def gluingContractGroundEquivClean (M : Matroid α) (X : Set α) :
    (Matroid.contract M X).E ≃ (M.E \ X : Set α) :=
  Equiv.setCongr (by simp)

/-- The restriction ground is the restricted set. -/
def gluingRestrictGroundEquivClean (M : Matroid α) (X : Set α) :
    (Matroid.restrict M X).E ≃ X :=
  Equiv.setCongr (by simp)

/--
Balanced-gluing activation for the complete nonempty proper tight branch in
rank three. Both tight ranks use the same point-pair gluing theorem; only the
construction of the rank-two factor and basis-lifting certificate differ.
-/
theorem exists_cyclicBasisOrder3_of_nonempty_proper_tight_gluing_clean
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  rcases
      (nonempty_proper_tight_flat_classification
        M k hE hRank hEcard hk hDense
        hX hXnonempty hXproper).2 with
    hOne | hTwo
  · -- rank-one tight set: points are `X`, pairs come from `M / X`.
    have hXcard : X.encard = (k : ℕ∞) := hOne.2
    have hsum :
        X.encard + (M.E \ X).encard = M.E.encard := by
      rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
        Set.union_sdiff_cancel hX.1]
    have hComplementCard :
        (M.E \ X).encard = ((2 * k : ℕ) : ℕ∞) := by
      apply ENat.add_right_injective_of_ne_top
        (by simp : (k : ℕ∞) ≠ ⊤)
      calc
        (k : ℕ∞) + (M.E \ X).encard =
            X.encard + (M.E \ X).encard := by rw [hXcard]
        _ = M.E.encard := hsum
        _ = ((3 * k : ℕ) : ℕ∞) := hEcard
        _ = (k : ℕ∞) + ((2 * k : ℕ) : ℕ∞) := by
          rw [← ENat.natCast_add]
          congr 1
          omega
    have hXfinite : X.Finite := hE.subset hX.1
    have hComplementFinite : (M.E \ X).Finite :=
      hE.subset Set.sdiff_subset
    let : Fintype X := hXfinite.fintype
    let : Fintype (M.E \ X : Set α) := hComplementFinite.fintype
    let : Fintype (Matroid.contract M X).E :=
      Fintype.ofEquiv (M.E \ X : Set α)
        (gluingContractGroundEquivClean M X).symm
    let : DecidableEq (Matroid.contract M X).E := Classical.decEq _
    have hXncard : X.ncard = k := by
      have hcast : (X.ncard : ℕ∞) = (k : ℕ∞) := by
        rw [hXfinite.cast_ncard_eq]
        exact hXcard
      exact_mod_cast hcast
    have hComplementNcard : (M.E \ X).ncard = 2 * k := by
      have hcast :
          ((M.E \ X).ncard : ℕ∞) = ((2 * k : ℕ) : ℕ∞) := by
        rw [hComplementFinite.cast_ncard_eq]
        exact hComplementCard
      exact_mod_cast hcast
    have hContractCard :
        Fintype.card (Matroid.contract M X).E = 2 * k := by
      calc
        Fintype.card (Matroid.contract M X).E =
            Fintype.card (M.E \ X : Set α) :=
          Fintype.card_congr (gluingContractGroundEquivClean M X)
        _ = Nat.card (M.E \ X : Set α) := Fintype.card_eq_nat_card
        _ = (M.E \ X).ncard := by simp only [Nat.card_coe_set_eq]
        _ = 2 * k := hComplementNcard
    have hContractDense : UniformlyDense (Matroid.contract M X) k :=
      UniformlyDense.contract_tight_rank_one M k hDense hX hOne.1
    have hContractRank : (Matroid.contract M X).eRank = 2 :=
      eRank_contract_eq_two_of_eRank_eq_three_eRk_eq_one
        M hRank hX.1 hOne.1
    have hLoopless : M.Loopless :=
      loopless_of_uniformlyDense M k hk hDense
    obtain ⟨rankTwoOrder, hadj⟩ :=
      HalfWeave.exists_cyclic_adjacent_base_order_of_uniformlyDense_direct
        (Matroid.contract M X) k hk hContractCard
        hContractDense hContractRank
    have hXNatCard : Nat.card X = k := by
      simpa only [Nat.card_coe_set_eq] using hXncard
    let points : Fin k ≃ X :=
      (Finite.equivFinOfCardEq hXNatCard).symm
    let pairs : Fin k × Bool ≃ (M.E \ X : Set α) :=
      rankTwoOrder.trans (gluingContractGroundEquivClean M X)
    have hpairs_coe (p : Fin k × Bool) :
        (pairs p : α) =
          ((rankTwoOrder p : (Matroid.contract M X).E) : α) := by
      rfl
    have hpointBasis (j : Fin k) :
        M.IsBasis ({(points j : α)} : Set α) X :=
      isBasis_singleton_of_loopless_eRk_eq_one
        M hLoopless hX.1 hOne.1 (points j).property
    have hpairWithin (i : Fin k) :
        (Matroid.contract M X).IsBase
          ({(pairs (i, false) : α),
            (pairs (i, true) : α)} : Set α) := by
      rw [hpairs_coe (i, false), hpairs_coe (i, true)]
      simpa [HalfWeave.weaveNext] using hadj (i, false)
    have hpairAcross (i : Fin k) :
        (Matroid.contract M X).IsBase
          ({(pairs (i, true) : α),
            (pairs (cyclicIndex k hk i 1, false) : α)} : Set α) := by
      rw [hpairs_coe (i, true),
        hpairs_coe (cyclicIndex k hk i 1, false)]
      simpa [HalfWeave.weaveNext,
        halfWeave_cyclicSucc_eq_cyclicIndex] using hadj (i, true)
    apply exists_cyclicBasisOrder3_of_point_pair_gluing_clean
      M hk Set.disjoint_sdiff_right (Set.union_sdiff_cancel hX.1)
      points pairs
    · intro i j
      exact isBase_insert_pair_of_contract_isBase_rank3
        M hRank hContractRank (hpointBasis j) (hpairWithin i)
    · intro i j
      exact isBase_insert_pair_of_contract_isBase_rank3
        M hRank hContractRank (hpointBasis j) (hpairAcross i)
  · -- rank-two tight flat: pairs are `X`, points are its complement.
    have hXflat : M.IsFlat X := tight_isFlat M k hE hDense hX
    have hXcard : X.encard = ((2 * k : ℕ) : ℕ∞) := hTwo.2
    have hsum :
        X.encard + (M.E \ X).encard = M.E.encard := by
      rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
        Set.union_sdiff_cancel hX.1]
    have hComplementCard : (M.E \ X).encard = (k : ℕ∞) := by
      apply ENat.add_right_injective_of_ne_top
        (ENat.natCast_ne_top (2 * k))
      calc
        ((2 * k : ℕ) : ℕ∞) + (M.E \ X).encard =
            X.encard + (M.E \ X).encard := by rw [hXcard]
        _ = M.E.encard := hsum
        _ = ((3 * k : ℕ) : ℕ∞) := hEcard
        _ = ((2 * k : ℕ) : ℕ∞) + (k : ℕ∞) := by
          rw [← ENat.natCast_add]
          congr 1
          omega
    have hRestrictRank : (M.restrict X).eRank = 2 := by
      rw [Matroid.eRank_def, Matroid.restrict_ground_eq,
        M.restrict_eRk_eq Set.Subset.rfl, hTwo.1]
    have hXfinite : X.Finite := hE.subset hXflat.subset_ground
    have hComplementFinite : (M.E \ X).Finite :=
      hE.subset Set.sdiff_subset
    let : Fintype X := hXfinite.fintype
    let : Fintype (M.E \ X : Set α) := hComplementFinite.fintype
    let : Fintype (M.restrict X).E :=
      Fintype.ofEquiv X (gluingRestrictGroundEquivClean M X).symm
    let : DecidableEq (M.restrict X).E := Classical.decEq _
    have hXncard : X.ncard = 2 * k := by
      have hcast :
          (X.ncard : ℕ∞) = ((2 * k : ℕ) : ℕ∞) := by
        rw [hXfinite.cast_ncard_eq]
        exact hXcard
      exact_mod_cast hcast
    have hRestrictCard : Fintype.card (M.restrict X).E = 2 * k := by
      calc
        Fintype.card (M.restrict X).E = Fintype.card X :=
          Fintype.card_congr (gluingRestrictGroundEquivClean M X)
        _ = Nat.card X := Fintype.card_eq_nat_card
        _ = X.ncard := by simp only [Nat.card_coe_set_eq]
        _ = 2 * k := hXncard
    have hRestrictDense : UniformlyDense (M.restrict X) k :=
      UniformlyDense.restrict M k hDense hXflat.subset_ground
    obtain ⟨rankTwoOrder, hadj⟩ :=
      HalfWeave.exists_cyclic_adjacent_base_order_of_uniformlyDense_direct
        (M.restrict X) k hk hRestrictCard hRestrictDense hRestrictRank
    have hComplementNcard : (M.E \ X).ncard = k := by
      have hcast : ((M.E \ X).ncard : ℕ∞) = (k : ℕ∞) := by
        rw [hComplementFinite.cast_ncard_eq]
        exact hComplementCard
      exact_mod_cast hcast
    have hComplementNatCard : Nat.card (M.E \ X : Set α) = k := by
      simpa only [Nat.card_coe_set_eq] using hComplementNcard
    let points : Fin k ≃ (M.E \ X : Set α) :=
      (Finite.equivFinOfCardEq hComplementNatCard).symm
    let pairs : Fin k × Bool ≃ X :=
      rankTwoOrder.trans (gluingRestrictGroundEquivClean M X)
    have hpairs_coe (p : Fin k × Bool) :
        (pairs p : α) = ((rankTwoOrder p : (M.restrict X).E) : α) := by
      rfl
    have hwithin_ne (i : Fin k) :
        (pairs (i, false) : α) ≠ (pairs (i, true) : α) := by
      intro h
      have hinput : (i, false) = (i, true) := pairs.injective (Subtype.ext h)
      have hbool := congrArg Prod.snd hinput
      simp at hbool
    have hacross_ne (i : Fin k) :
        (pairs (i, true) : α) ≠
          (pairs (cyclicIndex k hk i 1, false) : α) := by
      intro h
      have hinput :
          (i, true) = (cyclicIndex k hk i 1, false) :=
        pairs.injective (Subtype.ext h)
      have hbool := congrArg Prod.snd hinput
      simp at hbool
    have hpairWithin (i : Fin k) :
        M.IsBasis
          ({(pairs (i, false) : α),
            (pairs (i, true) : α)} : Set α) X := by
      apply (Matroid.isBase_restrict_iff hXflat.subset_ground).mp
      rw [hpairs_coe (i, false), hpairs_coe (i, true)]
      simpa [HalfWeave.weaveNext] using hadj (i, false)
    have hpairAcross (i : Fin k) :
        M.IsBasis
          ({(pairs (i, true) : α),
            (pairs (cyclicIndex k hk i 1, false) : α)} : Set α) X := by
      apply (Matroid.isBase_restrict_iff hXflat.subset_ground).mp
      rw [hpairs_coe (i, true),
        hpairs_coe (cyclicIndex k hk i 1, false)]
      simpa [HalfWeave.weaveNext,
        halfWeave_cyclicSucc_eq_cyclicIndex] using hadj (i, true)
    have hPQ : Disjoint (M.E \ X) X := Set.disjoint_sdiff_left
    have hUnion : (M.E \ X) ∪ X = M.E :=
      Set.sdiff_union_of_subset hXflat.subset_ground
    apply exists_cyclicBasisOrder3_of_point_pair_gluing_clean
      M hk hPQ hUnion points pairs
    · intro i j
      exact isBase_insert_pair_of_isBasis_flat_rank3
        M hRank hXflat (points j).property.1 (points j).property.2
        (hwithin_ne i) (hpairWithin i)
    · intro i j
      exact isBase_insert_pair_of_isBasis_flat_rank3
        M hRank hXflat (points j).property.1 (points j).property.2
        (hacross_ne i) (hpairAcross i)

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_point_pair_gluing_clean
#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_nonempty_proper_tight_gluing_clean

end

end Rank3KUM
