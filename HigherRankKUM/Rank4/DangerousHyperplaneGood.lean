import HigherRankKUM.Rank4.DangerousBranchT1Geometry
import HigherRankKUM.Rank4.DangerousBranchFactors
import HigherRankKUM.Rank4.CyclicPigeonhole
import HigherRankKUM.Rank4.CyclicWindowFour
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- Pure rank form of the key dangerous-hyperplane observation.

Let C have rank 2, 3, or 4 in a rank-four matroid. If adjoining each of the
overlapping triples {a,b,c} and {b,c,d} to C has full rank four, then at
least one of the three overlapping pairs {a,b}, {b,c}, {c,d} already raises
C to full rank four.

For a cyclic basis order of a dangerous hyperplane, this says that three
consecutive bad edges are impossible. -/
theorem one_of_three_pair_extensions_has_rank_four
    {M : Matroid α} {C : Set α} {a b c d : α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hC :
      M.eRk C = (2 : ℕ∞) ∨
      M.eRk C = (3 : ℕ∞) ∨
      M.eRk C = (4 : ℕ∞))
    (hABC : M.eRk (C ∪ ({a, b, c} : Set α)) = (4 : ℕ∞))
    (hBCD : M.eRk (C ∪ ({b, c, d} : Set α)) = (4 : ℕ∞)) :
    M.eRk (C ∪ ({a, b} : Set α)) = (4 : ℕ∞) ∨
    M.eRk (C ∪ ({b, c} : Set α)) = (4 : ℕ∞) ∨
    M.eRk (C ∪ ({c, d} : Set α)) = (4 : ℕ∞) := by
  let X : Set α := C ∪ ({a, b} : Set α)
  let Y : Set α := C ∪ ({b, c} : Set α)
  let Z : Set α := C ∪ ({c, d} : Set α)

  have hupper (S : Set α) : M.eRk S ≤ (4 : ℕ∞) := by
    rw [← hRank]
    exact M.eRk_le_eRank S

  have rank_nat_le_four (S : Set α) :
      ∃ r : ℕ, M.eRk S = (r : ℕ∞) ∧ r ≤ 4 := by
    obtain ⟨r, hr, hrle⟩ := ENat.le_natCast_iff.mp (hupper S)
    refine ⟨r, hr, ?_⟩
    exact_mod_cast hrle

  have rank_nat_le_three_of_ne_four
      (S : Set α) (hne : M.eRk S ≠ (4 : ℕ∞)) :
      ∃ r : ℕ, M.eRk S = (r : ℕ∞) ∧ r ≤ 3 := by
    obtain ⟨r, hr, hrle⟩ := rank_nat_le_four S
    refine ⟨r, hr, ?_⟩
    by_contra h
    have hr4 : r = 4 := by omega
    apply hne
    simpa [hr, hr4]

  rcases hC with hC2 | hC3 | hC4
  · by_contra hgood
    push_neg at hgood
    have hXbad : M.eRk X ≠ (4 : ℕ∞) := by
      simpa [X] using hgood.1
    have hYbad : M.eRk Y ≠ (4 : ℕ∞) := by
      simpa [Y] using hgood.2.1
    have hZbad : M.eRk Z ≠ (4 : ℕ∞) := by
      simpa [Z] using hgood.2.2

    obtain ⟨rx, hXr, hrx3⟩ :=
      rank_nat_le_three_of_ne_four X hXbad
    obtain ⟨ry, hYr, hry3⟩ :=
      rank_nat_le_three_of_ne_four Y hYbad
    obtain ⟨rz, hZr, hrz3⟩ :=
      rank_nat_le_three_of_ne_four Z hZbad

    have hXYunion : X ∪ Y = C ∪ ({a, b, c} : Set α) := by
      ext x
      simp [X, Y]
      tauto
    have hYZunion : Y ∪ Z = C ∪ ({b, c, d} : Set α) := by
      ext x
      simp [Y, Z]
      tauto
    have hCXY : C ⊆ X ∩ Y := by
      intro x hx
      exact ⟨Or.inl hx, Or.inl hx⟩
    have hCYZ : C ⊆ Y ∩ Z := by
      intro x hx
      exact ⟨Or.inl hx, Or.inl hx⟩

    obtain ⟨rxy, hXYr, hrxy4⟩ := rank_nat_le_four (X ∩ Y)
    obtain ⟨ryz, hYZr, hryz4⟩ := rank_nat_le_four (Y ∩ Z)
    have hxyLower := M.eRk_mono hCXY
    have hyzLower := M.eRk_mono hCYZ
    rw [hC2, hXYr] at hxyLower
    rw [hC2, hYZr] at hyzLower
    have hxyLowerNat : 2 ≤ rxy := by exact_mod_cast hxyLower
    have hyzLowerNat : 2 ≤ ryz := by exact_mod_cast hyzLower

    have hsubXY := M.eRk_inter_add_eRk_union_le X Y
    rw [hXYr, hXYunion, hABC, hXr, hYr] at hsubXY
    have hsubXYNat : rxy + 4 ≤ rx + ry := by exact_mod_cast hsubXY
    have hrx : rx = 3 := by omega
    have hry : ry = 3 := by omega
    have hrxy : rxy = 2 := by omega

    have hsubYZ := M.eRk_inter_add_eRk_union_le Y Z
    rw [hYZr, hYZunion, hBCD, hYr, hZr] at hsubYZ
    have hsubYZNat : ryz + 4 ≤ ry + rz := by exact_mod_cast hsubYZ
    have hrz : rz = 3 := by omega
    have hryz : ryz = 2 := by omega

    let B : Set α := C ∪ ({b} : Set α)
    let D : Set α := C ∪ ({c} : Set α)
    have hBXY : B ⊆ X ∩ Y := by
      intro x hx
      rcases hx with hxC | hxb
      · exact ⟨Or.inl hxC, Or.inl hxC⟩
      · have : x = b := by simpa [B] using hxb
        subst x
        simp [X, Y]
    have hDYZ : D ⊆ Y ∩ Z := by
      intro x hx
      rcases hx with hxC | hxc
      · exact ⟨Or.inl hxC, Or.inl hxC⟩
      · have : x = c := by simpa [D] using hxc
        subst x
        simp [Y, Z]
    have hCB : C ⊆ B := by
      intro x hx
      exact Or.inl hx
    have hCD : C ⊆ D := by
      intro x hx
      exact Or.inl hx

    have hB_le : M.eRk B ≤ (2 : ℕ∞) := by
      calc
        M.eRk B ≤ M.eRk (X ∩ Y) := M.eRk_mono hBXY
        _ = (2 : ℕ∞) := by
          rw [hXYr, hrxy]
          norm_num
    have hB_ge : (2 : ℕ∞) ≤ M.eRk B := by
      rw [← hC2]
      exact M.eRk_mono hCB
    have hBrank : M.eRk B = (2 : ℕ∞) :=
      le_antisymm hB_le hB_ge

    have hD_le : M.eRk D ≤ (2 : ℕ∞) := by
      calc
        M.eRk D ≤ M.eRk (Y ∩ Z) := M.eRk_mono hDYZ
        _ = (2 : ℕ∞) := by
          rw [hYZr, hryz]
          norm_num
    have hD_ge : (2 : ℕ∞) ≤ M.eRk D := by
      rw [← hC2]
      exact M.eRk_mono hCD
    have hDrank : M.eRk D = (2 : ℕ∞) :=
      le_antisymm hD_le hD_ge

    have hBDunion : B ∪ D = Y := by
      ext x
      simp [B, D, Y]
      tauto
    have hCBD : C ⊆ B ∩ D := by
      intro x hx
      exact ⟨Or.inl hx, Or.inl hx⟩
    obtain ⟨rbd, hBDr, hrbd4⟩ := rank_nat_le_four (B ∩ D)
    have hbdLower := M.eRk_mono hCBD
    rw [hC2, hBDr] at hbdLower
    have hbdLowerNat : 2 ≤ rbd := by exact_mod_cast hbdLower
    have hsubBD := M.eRk_inter_add_eRk_union_le B D
    rw [hBDr, hBDunion, hYr, hry, hBrank, hDrank] at hsubBD
    have hsubBDNat : rbd + 3 ≤ 2 + 2 := by exact_mod_cast hsubBD
    omega

  · by_contra hgood
    push_neg at hgood
    have hXbad : M.eRk X ≠ (4 : ℕ∞) := by
      simpa [X] using hgood.1
    have hYbad : M.eRk Y ≠ (4 : ℕ∞) := by
      simpa [Y] using hgood.2.1
    obtain ⟨rx, hXr, hrx3⟩ :=
      rank_nat_le_three_of_ne_four X hXbad
    obtain ⟨ry, hYr, hry3⟩ :=
      rank_nat_le_three_of_ne_four Y hYbad
    have hXYunion : X ∪ Y = C ∪ ({a, b, c} : Set α) := by
      ext x
      simp [X, Y]
      tauto
    have hCXY : C ⊆ X ∩ Y := by
      intro x hx
      exact ⟨Or.inl hx, Or.inl hx⟩
    obtain ⟨rxy, hXYr, hrxy4⟩ := rank_nat_le_four (X ∩ Y)
    have hxyLower := M.eRk_mono hCXY
    rw [hC3, hXYr] at hxyLower
    have hxyLowerNat : 3 ≤ rxy := by exact_mod_cast hxyLower
    have hsubXY := M.eRk_inter_add_eRk_union_le X Y
    rw [hXYr, hXYunion, hABC, hXr, hYr] at hsubXY
    have hsubXYNat : rxy + 4 ≤ rx + ry := by exact_mod_cast hsubXY
    omega

  · left
    apply le_antisymm
    · exact hupper _
    · rw [← hC4]
      exact M.eRk_mono (by
        intro x hx
        exact Or.inl hx)


/-- A core edge is good for a chosen dangerous hyperplane when adjoining its
two core endpoints to the complement has ambient rank four. -/
def DangerousHyperplaneEdgeGood
    {M : Matroid α} {k : ℕ} {H : Set α}
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (i : Fin (3 * k + 1)) : Prop :=
  M.eRk
      ((M.E \ H) ∪
        ({(order i : α),
          (order (cyclicIndex (3 * k + 1) (by omega) i 1) : α)} : Set α)) =
    (4 : ℕ∞)

/-- Three consecutive entries of a rank-three CBO of the dangerous
hyperplane form an ambient basis of that hyperplane. -/
theorem dangerous_hyperplane_core_triple_isBasis
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (i : Fin (3 * k + 1)) :
    M.IsBasis
      ({(order i : α),
        (order (cyclicIndex (3 * k + 1) (by omega) i 1) : α),
        (order (cyclicIndex (3 * k + 1) (by omega) i 2) : α)} : Set α)
      H := by
  have hB := hOrder i
  rw [cyclicWindow_three_eq] at hB
  exact (M.isBase_restrict_iff hH.subset_ground).1 hB

/-- Any basis of a dangerous hyperplane together with the whole complement
has ambient rank four. -/
theorem dangerous_hyperplane_basis_union_complement_rank_four
    {M : Matroid α} {k : ℕ} {H I : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hH : DangerousHyperplane M k H)
    (hI : M.IsBasis I H) :
    M.eRk ((M.E \ H) ∪ I) = (4 : ℕ∞) := by
  let C : Set α := M.E \ H
  have hCfin : C.Finite := by
    dsimp [C]
    exact hE.sdiff
  have hCcard : C.ncard = k + 1 := by
    dsimp [C]
    exact dangerous_complement_ncard_eq hE hEcard hH
  have hCnonempty : C.Nonempty := by
    rw [← Set.ncard_pos hCfin, hCcard]
    omega
  obtain ⟨c, hc⟩ := hCnonempty
  have hbase :=
    dangerous_one_hyperplane_basis_plus_complement_isBase
      hRank hH hI (by simpa [C] using hc)
  have hsub : insert c I ⊆ C ∪ I := by
    intro x hx
    rcases hx with rfl | hxI
    · exact Or.inl hc
    · exact Or.inr hxI
  have hlower := M.eRk_mono hsub
  have hbaseRank : M.eRk (insert c I) = (4 : ℕ∞) := by
    rw [hbase.eRk_eq_eRank, hRank]
  rw [hbaseRank] at hlower
  apply le_antisymm
  · rw [← hRank]
    exact M.eRk_le_eRank _
  · simpa [C] using hlower



/-- Every adjacent pair in the rank-three core CBO is an independent
rank-two set in the ambient matroid. -/
theorem dangerous_hyperplane_core_pair_indep_rank_two
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 1 ≤ k)
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (i : Fin (3 * k + 1)) :
    let P : Set α :=
      {(order i : α),
        (order (cyclicIndex (3 * k + 1) (by omega) i 1) : α)}
    M.Indep P ∧ M.eRk P = (2 : ℕ∞) := by
  let hn : 0 < 3 * k + 1 := by omega
  let j := cyclicIndex (3 * k + 1) hn i 1
  let P : Set α := {(order i : α), (order j : α)}
  have hTriple :=
    dangerous_hyperplane_core_triple_isBasis
      hH order hOrder i
  have hPsub :
      P ⊆
        ({(order i : α),
          (order (cyclicIndex (3 * k + 1) hn i 1) : α),
          (order (cyclicIndex (3 * k + 1) hn i 2) : α)} : Set α) := by
    intro x hx
    rcases hx with rfl | hx
    · simp
    · have hxj : x = (order j : α) := by simpa [P] using hx
      subst x
      simp [j]
  have hPind : M.Indep P := hTriple.indep.subset hPsub
  have hij : i ≠ j := by
    intro h
    exact cyclicIndex_ne_self_of_pos_of_lt
      (3 * k + 1) hn i (a := 1) (by omega) (by omega) h.symm
  have hvals : (order i : α) ≠ (order j : α) := by
    intro h
    apply hij
    apply order.injective
    exact Subtype.ext h
  have hPrank : M.eRk P = (2 : ℕ∞) := by
    rw [hPind.eRk_eq_encard]
    simpa [P] using Set.encard_pair hvals
  simpa [P, j, hn] using And.intro hPind hPrank

/-- A rank-two base selected inside the complement-restricted contraction
lifts directly to an ambient rank-four base together with the contracted
independent rank-two core pair. -/
theorem ambient_isBase_of_restricted_contract_base
    {M : Matroid α} {P C B : Set α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hP : M.Indep P)
    (hPrank : M.eRk P = (2 : ℕ∞))
    (hNrank : ((M.contract P).restrict C).eRank = (2 : ℕ∞))
    (hB : ((M.contract P).restrict C).IsBase B) :
    M.IsBase (B ∪ P) := by
  have hBindContract : (M.contract P).Indep B :=
    hB.indep.of_restrict
  have hcontractData := hP.contract_indep_iff.1 hBindContract
  have hDisj : Disjoint B P := hcontractData.1
  have hUnionInd : M.Indep (B ∪ P) := hcontractData.2
  have hPcard : P.encard = (2 : ℕ∞) := by
    have h := hPrank
    rw [hP.eRk_eq_encard] at h
    exact h
  have hBcard : B.encard = (2 : ℕ∞) := by
    rw [hB.encard_eq_eRank, hNrank]
  have hUnionCard : (B ∪ P).encard = (4 : ℕ∞) := by
    rw [Set.encard_union_eq hDisj, hBcard, hPcard]
    norm_num
  have hUnionFinite : (B ∪ P).Finite :=
    Set.finite_of_encard_eq_coe hUnionCard
  apply hUnionInd.isBase_of_eRk_ge hUnionFinite
  rw [hRank, hUnionInd.eRk_eq_encard, hUnionCard]

/-- Every three consecutive core-edge positions of a dangerous-hyperplane CBO
contain a good edge. This is the matroid input for the 3k+1 cyclic
pigeonhole lemma. -/
theorem dangerous_hyperplane_no_three_consecutive_bad_edges
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order) :
    ∀ i : Fin (3 * k + 1),
      DangerousHyperplaneEdgeGood order i ∨
      DangerousHyperplaneEdgeGood order
        (cyclicIndex (3 * k + 1) (by omega) i 1) ∨
      DangerousHyperplaneEdgeGood order
        (cyclicIndex (3 * k + 1) (by omega) i 2) := by
  intro i
  let n := 3 * k + 1
  let hn : 0 < n := by
    dsimp [n]
    omega
  let i1 : Fin n := cyclicIndex n hn i 1
  let i2 : Fin n := cyclicIndex n hn i 2
  let i3 : Fin n := cyclicIndex n hn i 3
  let a : α := (order i : α)
  let b : α := (order i1 : α)
  let c : α := (order i2 : α)
  let d : α := (order i3 : α)
  let C : Set α := M.E \ H

  have hCrank :
      M.eRk C = (2 : ℕ∞) ∨
      M.eRk C = (3 : ℕ∞) ∨
      M.eRk C = (4 : ℕ∞) := by
    simpa [C] using
      dangerous_complement_rank_trichotomy
        hE hRank hEcard hStrict hH

  have hBasis0 :=
    dangerous_hyperplane_core_triple_isBasis
      hH order hOrder i
  have hABC :
      M.eRk (C ∪ ({a, b, c} : Set α)) = (4 : ℕ∞) := by
    have h :=
      dangerous_hyperplane_basis_union_complement_rank_four
        (by omega : 1 ≤ k) hE hRank hEcard hH hBasis0
    simpa [C, a, b, c, i1, i2, n, hn] using h

  have hBasis1 :=
    dangerous_hyperplane_core_triple_isBasis
      hH order hOrder i1
  have hBCD :
      M.eRk (C ∪ ({b, c, d} : Set α)) = (4 : ℕ∞) := by
    have h :=
      dangerous_hyperplane_basis_union_complement_rank_four
        (by omega : 1 ≤ k) hE hRank hEcard hH hBasis1
    simpa [C, b, c, d, i1, i2, i3, n, hn, cyclicIndex_add,
      Nat.add_assoc] using h

  have hgood :=
    one_of_three_pair_extensions_has_rank_four
      hRank hCrank hABC hBCD
  rcases hgood with h0 | h1 | h2
  · left
    simpa [DangerousHyperplaneEdgeGood, C, a, b, i1, n, hn] using h0
  · right; left
    simpa [DangerousHyperplaneEdgeGood, C, b, c, i1, i2, n, hn,
      cyclicIndex_add, Nat.add_assoc] using h1
  · right; right
    simpa [DangerousHyperplaneEdgeGood, C, c, d, i2, i3, n, hn,
      cyclicIndex_add, Nat.add_assoc] using h2

/-- Any complement element together with three consecutive entries of a
rank-three CBO of the dangerous hyperplane forms an ambient basis. -/
theorem dangerous_hyperplane_complement_plus_core_triple_isBase
    {M : Matroid α} {k : ℕ} {H : Set α} {c : α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (hc : c ∈ M.E \ H)
    (q : Fin (3 * k + 1)) :
    M.IsBase
      ({c,
        (order q : α),
        (order (cyclicIndex (3 * k + 1) (by omega) q 1) : α),
        (order (cyclicIndex (3 * k + 1) (by omega) q 2) : α)} : Set α) := by
  have hBasis :=
    dangerous_hyperplane_core_triple_isBasis
      hH order hOrder q
  have h :=
    dangerous_one_hyperplane_basis_plus_complement_isBase
      hRank hH hBasis hc
  convert h using 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- A chosen dangerous hyperplane CBO has either two adjacent good core edges
or two good core edges separated by one edge. -/
theorem dangerous_hyperplane_exists_good_edge_configuration
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order) :
    ∃ i : Fin (3 * k + 1),
      (DangerousHyperplaneEdgeGood order i ∧
        DangerousHyperplaneEdgeGood order
          (cyclicIndex (3 * k + 1) (by omega) i 1)) ∨
      (DangerousHyperplaneEdgeGood order i ∧
        DangerousHyperplaneEdgeGood order
          (cyclicIndex (3 * k + 1) (by omega) i 2)) := by
  apply exists_adjacent_or_distance_two_good
    (k := k) (by omega)
    (DangerousHyperplaneEdgeGood order)
  exact dangerous_hyperplane_no_three_consecutive_bad_edges
    hk hE hRank hEcard hStrict hH order hOrder

end

end Rank4DangerousBranches
end HigherRankKUM
