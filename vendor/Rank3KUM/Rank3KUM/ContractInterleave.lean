import Rank3KUM.HalfWeave.CyclicBasisOrderingDirect
import Rank3KUM.Interleave
import Mathlib.Combinatorics.Matroid.Minor.Contract

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
A basis of a contraction by a rank-one set lifts, after adjoining a singleton
basis of the contracted set, to a basis of the original rank-three matroid.
-/
theorem isBase_insert_pair_of_contract_isBase_rank3
    (M : Matroid α) {X : Set α}
    (hRank : M.eRank = 3)
    (hContractRank : (Matroid.contract M X).eRank = 2)
    {e f g : α}
    (heBasis : M.IsBasis ({e} : Set α) X)
    (hpair : (Matroid.contract M X).IsBase
      ({f, g} : Set α)) :
    M.IsBase ({e, f, g} : Set α) := by
  have hdata :=
    heBasis.contract_indep_iff.mp hpair.indep
  have hset :
      ({f, g} : Set α) ∪ ({e} : Set α) =
        ({e, f, g} : Set α) := by
    ext x
    simp
  have htriple : M.Indep ({e, f, g} : Set α) := by
    rw [hset] at hdata
    exact hdata.1
  have heX : e ∈ X :=
    heBasis.subset (by simp)
  have heNot : e ∉ ({f, g} : Set α) := by
    intro he
    exact Set.disjoint_left.1 hdata.2 heX he
  have hpaircard :
      ({f, g} : Set α).encard = 2 :=
    hpair.encard_eq_eRank.trans hContractRank
  apply htriple.isBase_of_eRk_ge
    (Set.toFinite {e, f, g})
  rw [hRank, htriple.eRk_eq_encard,
    Set.encard_insert_of_notMem heNot, hpaircard]
  norm_num

/-- Contracted ground elements are value-identical to elements of the complement. -/
def contractGroundEquiv (M : Matroid α) (X : Set α) :
    (Matroid.contract M X).E ≃ (M.E \ X : Set α) where
  toFun e := ⟨e, by simpa using e.property⟩
  invFun e := ⟨e, by simp⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

@[simp] theorem contractGroundEquiv_trans_apply_coe
    {β : Type*} (M : Matroid α) (X : Set α)
    (σ : β ≃ (Matroid.contract M X).E) (x : β) :
    (((σ.trans (contractGroundEquiv M X)) x :
      (M.E \ X : Set α)) : α) =
      ((σ x : (Matroid.contract M X).E) : α) := by
  rfl

/-- Every point of a loopless rank-one set is a singleton basis of that set. -/
theorem isBasis_singleton_of_loopless_eRk_eq_one
    (M : Matroid α)
    (hLoopless : M.Loopless)
    {X : Set α}
    (hXsubset : X ⊆ M.E)
    (hXrank : M.eRk X = 1)
    {e : α}
    (heX : e ∈ X) :
    M.IsBasis ({e} : Set α) X := by
  let : M.Loopless := hLoopless
  have heNonloop : M.IsNonloop e :=
    Matroid.isNonloop_of_loopless (hXsubset heX)
  exact
    (heNonloop.indep.isBasis'_of_eRk_ge
      (by simp)
      (by simpa using heX)
      (by rw [hXrank, heNonloop.eRk_eq])).isBasis

/--
A cyclic adjacent-basis ordering of the rank-two contraction is the only
rank-two input needed by the rank-one tight branch.  The ordering and its
adjacency proof are passed directly rather than through an implementation
structure for the half-weave construction.
-/
theorem exists_cyclicBasisOrder3_of_contract_ordering
    (M : Matroid α) {X : Set α} {k : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 3)
    (hContractRank : (Matroid.contract M X).eRank = 2)
    (hXsubset : X ⊆ M.E)
    (hXrank : M.eRk X = 1)
    (hLoopless : M.Loopless)
    (points : Fin k ≃ X)
    (rankTwoOrder : Fin k × Bool ≃ (Matroid.contract M X).E)
    (hadj :
      ∀ p : Fin k × Bool,
        (Matroid.contract M X).IsBase
          ({((rankTwoOrder p : (Matroid.contract M X).E) : α),
            ((rankTwoOrder (HalfWeave.weaveNext k hk p) :
              (Matroid.contract M X).E) : α)} : Set α)) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  let pairs : Fin k × Bool ≃ (M.E \ X : Set α) :=
    rankTwoOrder.trans (contractGroundEquiv M X)
  have hpairs_coe (p : Fin k × Bool) :
      (pairs p : α) =
        ((rankTwoOrder p : (Matroid.contract M X).E) : α) := by
    exact contractGroundEquiv_trans_apply_coe
      M X rankTwoOrder p
  have hpointBasis (i : Fin k) :
      M.IsBasis ({(points i : α)} : Set α) X :=
    isBasis_singleton_of_loopless_eRk_eq_one
      M hLoopless hXsubset hXrank (points i).property
  have hwithin (i : Fin k) :
      (Matroid.contract M X).IsBase
        ({(pairs (i, false) : α),
          (pairs (i, true) : α)} : Set α) := by
    rw [hpairs_coe (i, false), hpairs_coe (i, true)]
    simpa [HalfWeave.weaveNext] using
      hadj (i, false)
  have hacross (i : Fin k) :
      (Matroid.contract M X).IsBase
        ({(pairs (i, true) : α),
          (pairs (cyclicIndex k hk i 1, false) : α)} : Set α) := by
    rw [hpairs_coe (i, true),
      hpairs_coe (cyclicIndex k hk i 1, false)]
    simpa [HalfWeave.weaveNext,
      halfWeave_cyclicSucc_eq_cyclicIndex] using
      hadj (i, true)
  have hDisjoint : Disjoint X (M.E \ X) :=
    Set.disjoint_sdiff_right
  have hLocal :
      CyclicBasisOrder3 M (by omega)
        (interleaveOneTwo hDisjoint points pairs) := by
    apply cyclicBasisOrder3_interleaveOneTwo
      M hk hDisjoint points pairs
    · intro i
      exact
        isBase_insert_pair_of_contract_isBase_rank3
          M hRank hContractRank (hpointBasis i) (hwithin i)
    · intro i
      have hbase :=
        isBase_insert_pair_of_contract_isBase_rank3
          M hRank hContractRank
          (hpointBasis (cyclicIndex k hk i 1))
          (hwithin i)
      convert hbase using 1
      ext x
      simp [or_comm, or_left_comm]
    · intro i
      have hbase :=
        isBase_insert_pair_of_contract_isBase_rank3
          M hRank hContractRank
          (hpointBasis (cyclicIndex k hk i 1))
          (hacross i)
      convert hbase using 1
      ext x
      simp [or_left_comm]
  have hUnion : X ∪ (M.E \ X) = M.E :=
    Set.union_sdiff_cancel hXsubset
  let order : Fin (3 * k) ≃ M.E :=
    (interleaveOneTwo hDisjoint points pairs).trans
      (Set.equivOfEq hUnion)
  refine ⟨order, ?_⟩
  intro i
  have hi := hLocal i
  simpa only [order, Equiv.trans_apply,
    Set.equivOfEq_apply] using hi

#print axioms Rank3KUM.isBase_insert_pair_of_contract_isBase_rank3
#print axioms Rank3KUM.contractGroundEquiv_trans_apply_coe
#print axioms Rank3KUM.isBasis_singleton_of_loopless_eRk_eq_one
#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_contract_ordering

/--
Contracting a rank-one set whose singleton basis is `e` lowers the rank of
every disjoint set union by exactly one.
-/
theorem eRk_union_eq_contract_eRk_add_one
    (M : Matroid α) {X A : Set α} {e : α}
    (heBasis : M.IsBasis ({e} : Set α) X)
    (hA : A ⊆ (Matroid.contract M X).E) :
    M.eRk (A ∪ X) =
      (Matroid.contract M X).eRk A + 1 := by
  obtain ⟨I, hI⟩ :=
    (Matroid.contract M X).exists_isBasis A
  have hI' :
      (Matroid.contract M ({e} : Set α)).IsBasis I A := by
    have h := hI
    rw [heBasis.contract_eq_contract_delete] at h
    exact h.of_delete
  have hLift :
      M.IsBasis (I ∪ ({e} : Set α))
        (A ∪ ({e} : Set α)) :=
    heBasis.indep.union_isBasis_union_of_contract_isBasis hI'
  have heX : e ∈ X :=
    heBasis.subset (by simp)
  have heI : e ∉ I := by
    intro he
    have heA : e ∈ A := hI.subset he
    have heComp : e ∈ M.E \ X := by
      simpa using hA heA
    exact heComp.2 heX
  have hclosure :
      M.closure (A ∪ ({e} : Set α)) =
        M.closure (A ∪ X) :=
    M.closure_union_congr_right heBasis.closure_eq_closure
  calc
    M.eRk (A ∪ X) =
        M.eRk (M.closure (A ∪ X)) :=
      (M.eRk_closure_eq _).symm
    _ = M.eRk (M.closure
        (A ∪ ({e} : Set α))) :=
      congrArg M.eRk hclosure.symm
    _ = M.eRk (A ∪ ({e} : Set α)) :=
      M.eRk_closure_eq _
    _ = (I ∪ ({e} : Set α)).encard :=
      hLift.encard_eq_eRk.symm
    _ = I.encard + 1 := by
      rw [Set.union_singleton,
        Set.encard_insert_of_notMem heI]
    _ = (Matroid.contract M X).eRk A + 1 := by
      rw [hI.encard_eq_eRk]

/-- Uniform density is inherited by contraction of a tight rank-one set. -/
theorem UniformlyDense.contract_tight_rank_one
    (M : Matroid α) (k : ℕ)
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXrank : M.eRk X = 1) :
    UniformlyDense (Matroid.contract M X) k := by
  obtain ⟨e, heX, heNonloop, hXclosure⟩ :=
    (Matroid.eRk_eq_one_iff hX.1).mp hXrank
  have heBasis : M.IsBasis ({e} : Set α) X :=
    heNonloop.indep.isBasis_of_subset_of_subset_closure
      (by simpa using heX) hXclosure
  have hXcard : X.encard = (k : ℕ∞) :=
    tight_encard_eq_k_of_eRk_eq_one M k hX hXrank
  intro A hA
  have hAcomp : A ⊆ M.E \ X := by
    simpa using hA
  have hAXsubset : A ∪ X ⊆ M.E :=
    Set.union_subset
      (hAcomp.trans Set.sdiff_subset) hX.1
  have hdisjoint : Disjoint A X :=
    Set.disjoint_sdiff_left.mono_left hAcomp
  have hdense := hDense (A ∪ X) hAXsubset
  have hrank :=
    eRk_union_eq_contract_eRk_add_one
      M heBasis hA
  rw [Set.encard_union_eq hdisjoint, hXcard,
    hrank, mul_add, mul_one] at hdense
  exact
    (ENat.add_le_add_iff_right
      (by simp : (k : ℕ∞) ≠ ⊤)).mp hdense

/-- Contracting a rank-one set from a rank-three matroid has rank two. -/
theorem eRank_contract_eq_two_of_eRank_eq_three_eRk_eq_one
    (M : Matroid α)
    (hRank : M.eRank = 3)
    {X : Set α}
    (hXsubset : X ⊆ M.E)
    (hXrank : M.eRk X = 1) :
    (Matroid.contract M X).eRank = 2 := by
  obtain ⟨e, heX, heNonloop, hXclosure⟩ :=
    (Matroid.eRk_eq_one_iff hXsubset).mp hXrank
  have heBasis : M.IsBasis ({e} : Set α) X :=
    heNonloop.indep.isBasis_of_subset_of_subset_closure
      (by simpa using heX) hXclosure
  have hrank :=
    eRk_union_eq_contract_eRk_add_one
      M heBasis
        (show (Matroid.contract M X).E ⊆
          (Matroid.contract M X).E from Set.Subset.rfl)
  rw [(Matroid.contract M X).eRk_ground,
    Matroid.contract_ground,
    Set.sdiff_union_of_subset hXsubset,
    M.eRk_ground, hRank] at hrank
  apply ENat.add_left_injective_of_ne_top
    (by simp : (1 : ℕ∞) ≠ ⊤)
  calc
    (Matroid.contract M X).eRank + 1 = 3 :=
      hrank.symm
    _ = (2 : ℕ∞) + 1 := by norm_num

/--
A nonempty tight rank-one set supplies the entire contraction/interleave branch
of the rank-three construction automatically.  The rank-two component is
consumed only through its cyclic adjacent-basis ordering interface.
-/
theorem exists_cyclicBasisOrder3_of_tight_rank_one
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXrank : M.eRk X = 1) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hXcard : X.encard = (k : ℕ∞) :=
    tight_encard_eq_k_of_eRk_eq_one M k hX hXrank
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
          X.encard + (M.E \ X).encard := by
        rw [hXcard]
      _ = M.E.encard := hsum
      _ = ((3 * k : ℕ) : ℕ∞) := hEcard
      _ = (k : ℕ∞) + ((2 * k : ℕ) : ℕ∞) := by
        rw [← ENat.natCast_add]
        congr 1
        omega
  have hXfinite : X.Finite :=
    hE.subset hX.1
  have hComplementFinite : (M.E \ X).Finite :=
    hE.subset Set.sdiff_subset
  let : Fintype X := hXfinite.fintype
  let : Fintype (M.E \ X : Set α) :=
    hComplementFinite.fintype
  let : Fintype (Matroid.contract M X).E :=
    Fintype.ofEquiv (M.E \ X : Set α)
      (contractGroundEquiv M X).symm
  let : DecidableEq (Matroid.contract M X).E :=
    Classical.decEq _
  have hXncard : X.ncard = k := by
    have hcast : (X.ncard : ℕ∞) = (k : ℕ∞) := by
      rw [hXfinite.cast_ncard_eq]
      exact hXcard
    exact_mod_cast hcast
  have hComplementNcard :
      (M.E \ X).ncard = 2 * k := by
    have hcast :
        ((M.E \ X).ncard : ℕ∞) =
          ((2 * k : ℕ) : ℕ∞) := by
      rw [hComplementFinite.cast_ncard_eq]
      exact hComplementCard
    exact_mod_cast hcast
  have hContractCard :
      Fintype.card (Matroid.contract M X).E = 2 * k := by
    calc
      Fintype.card (Matroid.contract M X).E =
          Fintype.card (M.E \ X : Set α) :=
        Fintype.card_congr (contractGroundEquiv M X)
      _ = Nat.card (M.E \ X : Set α) :=
        Fintype.card_eq_nat_card
      _ = (M.E \ X).ncard := by
        simp only [Nat.card_coe_set_eq]
      _ = 2 * k := hComplementNcard
  have hContractDense :
      UniformlyDense (Matroid.contract M X) k :=
    UniformlyDense.contract_tight_rank_one
      M k hDense hX hXrank
  have hContractRank :
      (Matroid.contract M X).eRank = 2 :=
    eRank_contract_eq_two_of_eRank_eq_three_eRk_eq_one
      M hRank hX.1 hXrank
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
  exact
    exists_cyclicBasisOrder3_of_contract_ordering
      M hk hRank hContractRank hX.1 hXrank
      hLoopless points rankTwoOrder hadj

#print axioms Rank3KUM.eRk_union_eq_contract_eRk_add_one
#print axioms Rank3KUM.UniformlyDense.contract_tight_rank_one
#print axioms Rank3KUM.eRank_contract_eq_two_of_eRank_eq_three_eRk_eq_one
#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_tight_rank_one

end

end Rank3KUM
