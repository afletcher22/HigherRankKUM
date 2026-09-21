import Rank3KUM.CyclicOrder
import Rank3KUM.HalfWeave.RankTwo
import Mathlib.Tactic

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
Within each three-position block, place one point first and the two entries of
the rank-two pair second and third.
-/
def finThreeInterleaveEquiv (k : ℕ) :
    Fin k × Fin 3 ≃ Fin k ⊕ (Fin k × Bool) where
  toFun x :=
    Fin.cases (Sum.inl x.1)
      (fun j =>
        Fin.cases (Sum.inr (x.1, false))
          (fun _ => Sum.inr (x.1, true)) j)
      x.2
  invFun
    | Sum.inl i => (i, 0)
    | Sum.inr (i, false) => (i, 1)
    | Sum.inr (i, true) => (i, 2)
  left_inv := by
    rintro ⟨i, j⟩
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    · rfl
    · rfl
    · fin_cases j
      rfl
  right_inv := by
    intro x
    rcases x with i | ⟨i, b⟩
    · rfl
    · cases b <;> rfl

@[simp] theorem finThreeInterleaveEquiv_zero
    (k : ℕ) (i : Fin k) :
    finThreeInterleaveEquiv k (i, 0) = Sum.inl i := by
  rfl

@[simp] theorem finThreeInterleaveEquiv_one
    (k : ℕ) (i : Fin k) :
    finThreeInterleaveEquiv k (i, 1) = Sum.inr (i, false) := by
  rfl

@[simp] theorem finThreeInterleaveEquiv_two
    (k : ℕ) (i : Fin k) :
    finThreeInterleaveEquiv k (i, 2) = Sum.inr (i, true) := by
  rfl

/-- The equivalence enumerating three-position blocks. -/
def interleavePositionEquiv (k : ℕ) :
    Fin k × Fin 3 ≃ Fin (3 * k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm 3 k)).symm

/-- The position of residue `j` in the `i`th three-element block. -/
def interleavePosition (k : ℕ) (i : Fin k) (j : Fin 3) :
    Fin (3 * k) :=
  (finCongr (Nat.mul_comm 3 k)).symm
    (finProdFinEquiv (i, j))

@[simp] theorem interleavePositionEquiv_apply
    (k : ℕ) (i : Fin k) (j : Fin 3) :
    interleavePositionEquiv k (i, j) =
      interleavePosition k i j := by
  rfl

@[simp] theorem interleavePosition_val
    (k : ℕ) (i : Fin k) (j : Fin 3) :
    (interleavePosition k i j).val = j.val + 3 * i.val := by
  rfl

/--
Interleave a `k`-element set with a `2k`-element set in blocks
`point, pair₀, pair₁`.
-/
def interleaveOneTwo
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X) :
    Fin (3 * k) ≃ (P ∪ X : Set α) := by
  classical
  exact
    (finCongr (Nat.mul_comm 3 k)).trans
      (finProdFinEquiv.symm.trans
        ((finThreeInterleaveEquiv k).trans
          ((Equiv.sumCongr points pairs).trans
            (Equiv.Set.union hPX).symm)))

/-- The first residue advances to the second within its block. -/
theorem cyclicIndex_interleave_zero_one
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 0) 1 =
      interleavePosition k i 1 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Two steps from the first residue reaches the third residue. -/
theorem cyclicIndex_interleave_zero_two
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 0) 2 =
      interleavePosition k i 2 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The second residue advances to the third within its block. -/
theorem cyclicIndex_interleave_one_one
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 1) 1 =
      interleavePosition k i 2 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Two steps from the second residue reaches the next block's point. -/
theorem cyclicIndex_interleave_one_two
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 1) 2 =
      interleavePosition k (cyclicIndex k hk i 1) 0 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  by_cases hi : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hieq : i.val + 1 = k := by omega
    have hwrap : (i.val + 1) % k = 0 := by
      rw [hieq, Nat.mod_self]
    have hnum :
        (1 : Fin 3).val + 3 * i.val + 2 = 3 * k := by
      norm_num
      omega
    rw [hnum, hwrap, Nat.mod_self]
    norm_num

/-- The third residue advances to the next block's point. -/
theorem cyclicIndex_interleave_two_one
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 2) 1 =
      interleavePosition k (cyclicIndex k hk i 1) 0 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  by_cases hi : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hieq : i.val + 1 = k := by omega
    have hwrap : (i.val + 1) % k = 0 := by
      rw [hieq, Nat.mod_self]
    have hnum :
        (2 : Fin 3).val + 3 * i.val + 1 = 3 * k := by
      norm_num
      omega
    rw [hnum, hwrap, Nat.mod_self]
    norm_num

/-- Two steps from the third residue reaches the next block's first pair entry. -/
theorem cyclicIndex_interleave_two_two
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 2) 2 =
      interleavePosition k (cyclicIndex k hk i 1) 1 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  by_cases hi : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hieq : i.val + 1 = k := by omega
    have hwrap : (i.val + 1) % k = 0 := by
      rw [hieq, Nat.mod_self]
    have hnum :
        (2 : Fin 3).val + 3 * i.val + 2 = 3 * k + 1 := by
      norm_num
      omega
    rw [hnum, hwrap]
    have hone_lt : 1 < 3 * k := by omega
    simp [Nat.mod_eq_of_lt hone_lt]

@[simp] theorem interleaveOneTwo_point
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (i : Fin k) :
    ((interleaveOneTwo hPX points pairs
      (interleavePosition k i 0) : (P ∪ X : Set α)) : α) =
      (points i : α) := by
  simp [interleaveOneTwo, interleavePosition]

@[simp] theorem interleaveOneTwo_pair_false
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (i : Fin k) :
    ((interleaveOneTwo hPX points pairs
      (interleavePosition k i 1) : (P ∪ X : Set α)) : α) =
      (pairs (i, false) : α) := by
  simp [interleaveOneTwo, interleavePosition]

@[simp] theorem interleaveOneTwo_pair_true
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (i : Fin k) :
    ((interleaveOneTwo hPX points pairs
      (interleavePosition k i 2) : (P ∪ X : Set α)) : α) =
      (pairs (i, true) : α) := by
  simp [interleaveOneTwo, interleavePosition]

/--
A basis of a rank-two flat extends to a basis of a rank-three matroid after
adjoining any ground element outside the flat.
-/
theorem isBase_insert_pair_of_isBasis_flat_rank3
    (M : Matroid α) {X : Set α}
    (hRank : M.eRank = 3)
    (hXflat : M.IsFlat X)
    {e f g : α}
    (heE : e ∈ M.E)
    (heX : e ∉ X)
    (hfg : f ≠ g)
    (hpair : M.IsBasis ({f, g} : Set α) X) :
    M.IsBase ({e, f, g} : Set α) := by
  have hepair : e ∉ ({f, g} : Set α) := by
    intro he
    exact heX (hpair.subset he)
  have hclosure : M.closure ({f, g} : Set α) = X := by
    calc
      M.closure ({f, g} : Set α) = M.closure X :=
        hpair.closure_eq_closure
      _ = X := (Matroid.isFlat_iff_closure_eq.mp hXflat)
  have htriple : M.Indep ({e, f, g} : Set α) := by
    exact
      (hpair.indep.insert_indep_iff_of_notMem hepair).2
        ⟨heE, by simpa [hclosure] using heX⟩
  apply htriple.isBase_of_eRk_ge (Set.toFinite {e, f, g})
  rw [hRank, htriple.eRk_eq_encard,
    Set.encard_insert_of_notMem hepair,
    Set.encard_pair hfg]
  norm_num

/--
If each point with its pair, each pair with the next point, and the shifted
pair-point-pair window are bases, the interleaved enumeration is cyclic.
-/
theorem cyclicBasisOrder3_interleaveOneTwo
    (M : Matroid α) {P X : Set α} {k : ℕ}
    (hk : 0 < k)
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (hzero : ∀ i : Fin k,
      M.IsBase
        ({(points i : α),
          (pairs (i, false) : α),
          (pairs (i, true) : α)} : Set α))
    (hone : ∀ i : Fin k,
      M.IsBase
        ({(pairs (i, false) : α),
          (pairs (i, true) : α),
          (points (cyclicIndex k hk i 1) : α)} : Set α))
    (htwo : ∀ i : Fin k,
      M.IsBase
        ({(pairs (i, true) : α),
          (points (cyclicIndex k hk i 1) : α),
          (pairs (cyclicIndex k hk i 1, false) : α)} : Set α)) :
    CyclicBasisOrder3 M (by omega)
      (interleaveOneTwo hPX points pairs) := by
  intro pos
  obtain ⟨⟨i, j⟩, rfl⟩ :=
    (interleavePositionEquiv k).surjective pos
  have hj :
      j = (0 : Fin 3) ∨ j = (1 : Fin 3) ∨ j = (2 : Fin 3) := by
    fin_cases j
    · left
      apply Fin.ext
      rfl
    · right
      left
      apply Fin.ext
      rfl
    · right
      right
      apply Fin.ext
      rfl
  rcases hj with rfl | rfl | rfl
  · rw [interleavePositionEquiv_apply,
      cyclicIndex_interleave_zero_one k hk i,
      cyclicIndex_interleave_zero_two k hk i]
    simpa using hzero i
  · rw [interleavePositionEquiv_apply,
      cyclicIndex_interleave_one_one k hk i,
      cyclicIndex_interleave_one_two k hk i]
    simpa using hone i
  · rw [interleavePositionEquiv_apply,
      cyclicIndex_interleave_two_one k hk i,
      cyclicIndex_interleave_two_two k hk i]
    simpa using htwo i

#print axioms Rank3KUM.cyclicBasisOrder3_interleaveOneTwo

/--
A cyclic adjacent-basis order on a rank-two flat interleaves with any
enumeration of outside points to give a cyclic rank-three basis order.
-/
theorem cyclicBasisOrder3_interleaveOneTwo_of_flat_pairs
    (M : Matroid α) {P X : Set α} {k : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 3)
    (hPX : Disjoint P X)
    (hPground : P ⊆ M.E)
    (hXflat : M.IsFlat X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (hwithin : ∀ i : Fin k,
      M.IsBasis
        ({(pairs (i, false) : α),
          (pairs (i, true) : α)} : Set α) X)
    (hacross : ∀ i : Fin k,
      M.IsBasis
        ({(pairs (i, true) : α),
          (pairs (cyclicIndex k hk i 1, false) : α)} : Set α) X) :
    CyclicBasisOrder3 M (by omega)
      (interleaveOneTwo hPX points pairs) := by
  have hpoint_ground (i : Fin k) :
      (points i : α) ∈ M.E :=
    hPground (points i).property
  have hpoint_not_mem (i : Fin k) :
      (points i : α) ∉ X := by
    intro hiX
    exact Set.disjoint_left.1 hPX (points i).property hiX
  have hwithin_ne (i : Fin k) :
      (pairs (i, false) : α) ≠
        (pairs (i, true) : α) := by
    intro h
    have hinput :
        (i, false) = (i, true) :=
      pairs.injective (Subtype.ext h)
    have hbool := congrArg Prod.snd hinput
    simp at hbool
  have hacross_ne (i : Fin k) :
      (pairs (i, true) : α) ≠
        (pairs (cyclicIndex k hk i 1, false) : α) := by
    intro h
    have hinput :
        (i, true) =
          (cyclicIndex k hk i 1, false) :=
      pairs.injective (Subtype.ext h)
    have hbool := congrArg Prod.snd hinput
    simp at hbool
  apply cyclicBasisOrder3_interleaveOneTwo
    M hk hPX points pairs
  · intro i
    exact
      isBase_insert_pair_of_isBasis_flat_rank3
        M hRank hXflat
        (hpoint_ground i) (hpoint_not_mem i)
        (hwithin_ne i) (hwithin i)
  · intro i
    have hbase :=
      isBase_insert_pair_of_isBasis_flat_rank3
        M hRank hXflat
        (hpoint_ground (cyclicIndex k hk i 1))
        (hpoint_not_mem (cyclicIndex k hk i 1))
        (hwithin_ne i) (hwithin i)
    convert hbase using 1
    ext x
    simp [or_comm, or_left_comm]
  · intro i
    have hbase :=
      isBase_insert_pair_of_isBasis_flat_rank3
        M hRank hXflat
        (hpoint_ground (cyclicIndex k hk i 1))
        (hpoint_not_mem (cyclicIndex k hk i 1))
        (hacross_ne i) (hacross i)
    convert hbase using 1
    ext x
    simp [or_left_comm]

#print axioms Rank3KUM.isBase_insert_pair_of_isBasis_flat_rank3
#print axioms Rank3KUM.cyclicBasisOrder3_interleaveOneTwo_of_flat_pairs

/-- Restriction ground elements and elements of the restricted set are value-identical. -/
def restrictGroundEquiv (M : Matroid α) (X : Set α) :
    (Matroid.restrict M X).E ≃ X where
  toFun e := ⟨e, by simpa using e.property⟩
  invFun e := ⟨e, by simp⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

@[simp] theorem restrictGroundEquiv_coe
    (M : Matroid α) (X : Set α)
    (e : (Matroid.restrict M X).E) :
    ((restrictGroundEquiv M X e : X) : α) = e := by
  rfl

@[simp] theorem restrictGroundEquiv_trans_apply_coe
    {β : Type*} (M : Matroid α) (X : Set α)
    (σ : β ≃ (Matroid.restrict M X).E) (x : β) :
    (((σ.trans (restrictGroundEquiv M X)) x : X) : α) =
      ((σ x : (Matroid.restrict M X).E) : α) := by
  rfl

/-- The half-weave successor is the same cyclic successor used by interleaving. -/
theorem halfWeave_cyclicSucc_eq_cyclicIndex
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    HalfWeave.cyclicSucc k hk i =
      cyclicIndex k hk i 1 := by
  apply Fin.ext
  simp [HalfWeave.cyclicSucc_val, cyclicIndex_val]

/--
A sorted rank-two enumeration supplies exactly the two pair-basis families
needed by the rank-three flat interleave.
-/
theorem cyclicBasisOrder3_interleaveOneTwo_of_sortedEnumeration
    (M : Matroid α) {P X : Set α} {k m : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 3)
    (hRestrictRank : (Matroid.restrict M X).eRank = 2)
    (hPX : Disjoint P X)
    (hPground : P ⊆ M.E)
    (hXflat : M.IsFlat X)
    (points : Fin k ≃ P)
    (D : HalfWeave.RankTwoSortedEnumeration
      (Matroid.restrict M X) k m) :
    CyclicBasisOrder3 M (by omega)
      (interleaveOneTwo hPX points
        ((HalfWeave.rankTwoWoven D hk).trans
          (restrictGroundEquiv M X))) := by
  let pairs : Fin k × Bool ≃ X :=
    (HalfWeave.rankTwoWoven D hk).trans
      (restrictGroundEquiv M X)
  have hpairs_coe (p : Fin k × Bool) :
      (pairs p : α) =
        ((HalfWeave.rankTwoWoven D hk p :
          (Matroid.restrict M X).E) : α) := by
    change
      ((((HalfWeave.rankTwoWoven D hk).trans
        (restrictGroundEquiv M X)) p : X) : α) =
        ((HalfWeave.rankTwoWoven D hk p :
          (Matroid.restrict M X).E) : α)
    exact restrictGroundEquiv_trans_apply_coe
      M X (HalfWeave.rankTwoWoven D hk) p
  change CyclicBasisOrder3 M (by omega)
    (interleaveOneTwo hPX points pairs)
  apply cyclicBasisOrder3_interleaveOneTwo_of_flat_pairs
    M hk hRank hPX hPground hXflat points pairs
  · intro i
    apply (Matroid.isBase_restrict_iff hXflat.subset_ground).mp
    rw [hpairs_coe (i, false), hpairs_coe (i, true)]
    simpa using
      (HalfWeave.rankTwoWoven_successor_isBase
        (Matroid.restrict M X) D hk hRestrictRank (i, false))
  · intro i
    apply (Matroid.isBase_restrict_iff hXflat.subset_ground).mp
    rw [hpairs_coe (i, true),
      hpairs_coe (cyclicIndex k hk i 1, false)]
    simpa [halfWeave_cyclicSucc_eq_cyclicIndex] using
      (HalfWeave.rankTwoWoven_successor_isBase
        (Matroid.restrict M X) D hk hRestrictRank (i, true))

#print axioms Rank3KUM.restrictGroundEquiv_coe
#print axioms Rank3KUM.restrictGroundEquiv_trans_apply_coe
#print axioms Rank3KUM.halfWeave_cyclicSucc_eq_cyclicIndex

#print axioms Rank3KUM.cyclicBasisOrder3_interleaveOneTwo_of_sortedEnumeration

/--
Transport the interleaved order from the partition
`(M.E \ X) ∪ X` back to the ground set.
-/
theorem exists_cyclicBasisOrder3_of_sortedEnumeration_flat
    (M : Matroid α) {X : Set α} {k m : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 3)
    (hRestrictRank : (Matroid.restrict M X).eRank = 2)
    (hXflat : M.IsFlat X)
    (points : Fin k ≃ (M.E \ X : Set α))
    (D : HalfWeave.RankTwoSortedEnumeration
      (Matroid.restrict M X) k m) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hPX : Disjoint (M.E \ X) X :=
    Set.disjoint_sdiff_left
  have hUnion : (M.E \ X) ∪ X = M.E :=
    Set.sdiff_union_of_subset hXflat.subset_ground
  let localOrder : Fin (3 * k) ≃
      ((M.E \ X) ∪ X : Set α) :=
    interleaveOneTwo hPX points
      ((HalfWeave.rankTwoWoven D hk).trans
        (restrictGroundEquiv M X))
  have hLocal : CyclicBasisOrder3 M (by omega) localOrder := by
    exact
      cyclicBasisOrder3_interleaveOneTwo_of_sortedEnumeration
        M hk hRank hRestrictRank hPX Set.sdiff_subset
        hXflat points D
  let order : Fin (3 * k) ≃ M.E :=
    localOrder.trans (Equiv.setCongr hUnion)
  refine ⟨order, ?_⟩
  intro i
  have hi := hLocal i
  simpa only [order, Equiv.trans_apply,
    Equiv.setCongr_apply] using hi


#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_sortedEnumeration_flat

/--
A cardinality proof for the complement supplies its enumeration automatically.
-/
theorem exists_cyclicBasisOrder3_of_sortedEnumeration_tight_flat
    (M : Matroid α) {X : Set α} {k m : ℕ}
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hRestrictRank : (Matroid.restrict M X).eRank = 2)
    (hXflat : M.IsFlat X)
    (hComplementCard : (M.E \ X).encard = (k : ℕ∞))
    (D : HalfWeave.RankTwoSortedEnumeration
      (Matroid.restrict M X) k m) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hComplementFinite : (M.E \ X).Finite :=
    hE.subset Set.sdiff_subset
  let : Fintype (M.E \ X : Set α) :=
    hComplementFinite.fintype
  have hNcard : (M.E \ X).ncard = k := by
    have hcast :
        ((M.E \ X).ncard : ℕ∞) = (k : ℕ∞) := by
      rw [hComplementFinite.cast_ncard_eq]
      exact hComplementCard
    exact_mod_cast hcast
  have hNatCard : Nat.card (M.E \ X : Set α) = k := by
    simpa only [Nat.card_coe_set_eq] using hNcard
  let points : Fin k ≃ (M.E \ X : Set α) :=
    (Finite.equivFinOfCardEq hNatCard).symm
  exact
    exists_cyclicBasisOrder3_of_sortedEnumeration_flat
      M hk hRank hRestrictRank hXflat points D

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_sortedEnumeration_tight_flat

end

end Rank3KUM
