import Rank3KUM.HalfWeave.CyclicBasisOrderingDirect
import Rank3KUM.Interleave

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
A cyclic adjacent-basis ordering of a rank-two restriction is the only
rank-two input needed by the rank-two tight branch.  The ordering and its
adjacency proof are passed directly rather than through an implementation
structure for the half-weave construction.
-/
theorem exists_cyclicBasisOrder3_of_flat_ordering
    (M : Matroid α) {X : Set α} {k : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 3)
    (hXflat : M.IsFlat X)
    (points : Fin k ≃ (M.E \ X : Set α))
    (rankTwoOrder : Fin k × Bool ≃ (M.restrict X).E)
    (hadj :
      ∀ p : Fin k × Bool,
        (M.restrict X).IsBase
          ({((rankTwoOrder p : (M.restrict X).E) : α),
            ((rankTwoOrder (HalfWeave.weaveNext k hk p) :
              (M.restrict X).E) : α)} : Set α)) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  let pairs : Fin k × Bool ≃ X :=
    rankTwoOrder.trans (restrictGroundEquiv M X)
  have hpairs_coe (p : Fin k × Bool) :
      (pairs p : α) =
        ((rankTwoOrder p : (M.restrict X).E) : α) := by
    exact restrictGroundEquiv_trans_apply_coe
      M X rankTwoOrder p
  have hwithin (i : Fin k) :
      M.IsBasis
        ({(pairs (i, false) : α),
          (pairs (i, true) : α)} : Set α) X := by
    apply (Matroid.isBase_restrict_iff hXflat.subset_ground).mp
    rw [hpairs_coe (i, false), hpairs_coe (i, true)]
    simpa [HalfWeave.weaveNext] using
      hadj (i, false)
  have hacross (i : Fin k) :
      M.IsBasis
        ({(pairs (i, true) : α),
          (pairs (cyclicIndex k hk i 1, false) : α)} : Set α) X := by
    apply (Matroid.isBase_restrict_iff hXflat.subset_ground).mp
    rw [hpairs_coe (i, true),
      hpairs_coe (cyclicIndex k hk i 1, false)]
    simpa [HalfWeave.weaveNext,
      halfWeave_cyclicSucc_eq_cyclicIndex] using
      hadj (i, true)
  have hPX : Disjoint (M.E \ X) X :=
    Set.disjoint_sdiff_left
  have hLocal :
      CyclicBasisOrder3 M (by omega)
        (interleaveOneTwo hPX points pairs) := by
    exact
      cyclicBasisOrder3_interleaveOneTwo_of_flat_pairs
        M hk hRank hPX Set.sdiff_subset hXflat points pairs
        hwithin hacross
  have hUnion : (M.E \ X) ∪ X = M.E :=
    Set.sdiff_union_of_subset hXflat.subset_ground
  let order : Fin (3 * k) ≃ M.E :=
    (interleaveOneTwo hPX points pairs).trans
      (Set.equivOfEq hUnion)
  refine ⟨order, ?_⟩
  intro i
  have hi := hLocal i
  simpa only [order, Equiv.trans_apply,
    Set.equivOfEq_apply] using hi

/--
A uniformly dense rank-two flat of size `2k`, with a complement of size `k`,
supplies exactly the cyclic adjacent-basis ordering needed by interleaving.
Retained as a compatibility endpoint; the active tight branch below constructs
the same rank-two ordering directly so this wrapper is not on the main proof path.
-/
theorem exists_cyclicBasisOrder3_of_uniformlyDense_rankTwo_flat
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hRestrictRank : (M.restrict X).eRank = 2)
    (hXflat : M.IsFlat X)
    (hXcard : X.encard = ((2 * k : ℕ) : ℕ∞))
    (hComplementCard : (M.E \ X).encard = (k : ℕ∞)) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hXfinite : X.Finite :=
    hE.subset hXflat.subset_ground
  have hComplementFinite : (M.E \ X).Finite :=
    hE.subset Set.sdiff_subset
  let : Fintype X := hXfinite.fintype
  let : Fintype (M.E \ X : Set α) :=
    hComplementFinite.fintype
  let : Fintype (M.restrict X).E :=
    Fintype.ofEquiv X (restrictGroundEquiv M X).symm
  let : DecidableEq (M.restrict X).E :=
    Classical.decEq _
  have hXncard : X.ncard = 2 * k := by
    have hcast : (X.ncard : ℕ∞) =
        ((2 * k : ℕ) : ℕ∞) := by
      rw [hXfinite.cast_ncard_eq]
      exact hXcard
    exact_mod_cast hcast
  have hRestrictCard :
      Fintype.card (M.restrict X).E = 2 * k := by
    calc
      Fintype.card (M.restrict X).E =
          Fintype.card X :=
        Fintype.card_congr (restrictGroundEquiv M X)
      _ = Nat.card X := Fintype.card_eq_nat_card
      _ = X.ncard := by
        simp only [Nat.card_coe_set_eq]
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
  exact
    exists_cyclicBasisOrder3_of_flat_ordering
      M hk hRank hXflat points rankTwoOrder hadj

/--
The rank-two side of the tight-set classification constructs exactly the
rank-two adjacent-basis ordering needed for interleaving.  The compatibility
wrapper above is deliberately bypassed on the active proof path.
-/
theorem exists_cyclicBasisOrder3_of_tight_rank_two
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXrank : M.eRk X = 2) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hXflat : M.IsFlat X :=
    tight_isFlat M k hE hDense hX
  have hXcard :
      X.encard = ((2 * k : ℕ) : ℕ∞) :=
    tight_encard_eq_two_mul_k_of_eRk_eq_two
      M k hX hXrank
  have hsum :
      X.encard + (M.E \ X).encard = M.E.encard := by
    rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
      Set.union_sdiff_cancel hX.1]
  have hComplementCard :
      (M.E \ X).encard = (k : ℕ∞) := by
    apply ENat.add_right_injective_of_ne_top
      (ENat.natCast_ne_top (2 * k))
    calc
      ((2 * k : ℕ) : ℕ∞) + (M.E \ X).encard =
          X.encard + (M.E \ X).encard := by
        rw [hXcard]
      _ = M.E.encard := hsum
      _ = ((3 * k : ℕ) : ℕ∞) := hEcard
      _ = ((2 * k : ℕ) : ℕ∞) + (k : ℕ∞) := by
        rw [← ENat.natCast_add]
        congr 1
        omega
  have hRestrictRank :
      (M.restrict X).eRank = 2 := by
    rw [Matroid.eRank_def,
      Matroid.restrict_ground_eq,
      M.restrict_eRk_eq Set.Subset.rfl, hXrank]
  have hXfinite : X.Finite :=
    hE.subset hXflat.subset_ground
  have hComplementFinite : (M.E \ X).Finite :=
    hE.subset Set.sdiff_subset
  let : Fintype X := hXfinite.fintype
  let : Fintype (M.E \ X : Set α) :=
    hComplementFinite.fintype
  let : Fintype (M.restrict X).E :=
    Fintype.ofEquiv X (restrictGroundEquiv M X).symm
  let : DecidableEq (M.restrict X).E :=
    Classical.decEq _
  have hXncard : X.ncard = 2 * k := by
    have hcast : (X.ncard : ℕ∞) =
        ((2 * k : ℕ) : ℕ∞) := by
      rw [hXfinite.cast_ncard_eq]
      exact hXcard
    exact_mod_cast hcast
  have hRestrictCard :
      Fintype.card (M.restrict X).E = 2 * k := by
    calc
      Fintype.card (M.restrict X).E =
          Fintype.card X :=
        Fintype.card_congr (restrictGroundEquiv M X)
      _ = Nat.card X := Fintype.card_eq_nat_card
      _ = X.ncard := by
        simp only [Nat.card_coe_set_eq]
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
  exact
    exists_cyclicBasisOrder3_of_flat_ordering
      M hk hRank hXflat points rankTwoOrder hadj

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_flat_ordering
#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_uniformlyDense_rankTwo_flat
#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_tight_rank_two

end

end Rank3KUM
