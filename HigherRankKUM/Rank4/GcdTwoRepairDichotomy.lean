import HigherRankKUM.Rank4.GcdTwoRepairMove
import HigherRankKUM.BinaryRelationLocalStructure
import HigherRankKUM.PairCycle

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

variable {α : Type*}

/-- A common-base repair is called `cross` when its new left block is neither
of the two old adjacent pair blocks.  Because every such common base is a
2-element subset of the four-element repair ground, this is exactly the
set-level distinction between a genuine one-from-each-side repartition and a
wholesale swap. -/
def IsCrossCommonBase
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) (Q : Set α) : Prop :=
  (leftRepairMinor A s).IsBase Q ∧
  (rightRepairMinor A s)✶.IsBase Q ∧
  Q ≠ A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) ∧
  Q ≠ A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s)

/-- The other possible nontrivial local common-base move is the wholesale
swap: the new left block is exactly the old right block. -/
def IsSwapCommonBase
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) (Q : Set α) : Prop :=
  (leftRepairMinor A s).IsBase Q ∧
  (rightRepairMinor A s)✶.IsBase Q ∧
  Q = A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s)

/-- Any nontrivial common base is either a genuine cross repair or the
wholesale opposite-block swap.  The exact four-element finite classification
shows that the swap-only situation is very rare, but this elementary
dichotomy itself needs no representability or enumeration. -/
theorem alternative_common_base_cross_or_swap
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) {Q : Set α}
    (hL : (leftRepairMinor A s).IsBase Q)
    (hR : (rightRepairMinor A s)✶.IsBase Q)
    (hne : Q ≠ A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s)) :
    IsCrossCommonBase A s Q ∨ IsSwapCommonBase A s Q := by
  by_cases hswap : Q = A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s)
  · exact Or.inr ⟨hL, hR, hswap⟩
  · exact Or.inl ⟨hL, hR, hne, hswap⟩

/-- A cross common base really contains one element from each of the two old
adjacent pair blocks.  This turns the extensional definition
`Q ≠ oldLeft, oldRight` into the concrete one-from-each-side form needed by
later parity and closure arguments. -/
theorem crossCommonBase_eq_pair_one_from_each
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (s : Fin N) {Q : Set α} (hcross : IsCrossCommonBase A s Q) :
    ∃ x y : α,
      x ∈ A.block (AdjacentRepair.leftBoundaryIndex N 2 hN s) ∧
      y ∈ A.block (AdjacentRepair.rightBoundaryIndex N 2 hN s) ∧
      Q = {x, y} := by
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  obtain ⟨q₀, q₁, r₀, r₁, hqne, _hrne, hQ, _hcomp, _hpart⟩ :=
    common_base_repartition_pair_decomposition A h2N s hcross.1 hcross.2.1
  have hQsub : Q ⊆ repairGround A s := by
    have hsub := hcross.1.subset_ground
    simpa [leftRepairMinor, LocalRepairClosure.boundaryMinor] using hsub
  have hq₀Q : q₀ ∈ Q := by rw [hQ]; simp
  have hq₁Q : q₁ ∈ Q := by rw [hQ]; simp
  have hq₀rg := hQsub hq₀Q
  have hq₁rg := hQsub hq₁Q
  simp only [repairGround] at hq₀rg hq₁rg
  have hpair_eq_of_mem (k : Fin N) {x y : α} (hxy : x ≠ y)
      (hx : x ∈ A.block k) (hy : y ∈ A.block k) :
      ({x, y} : Set α) = A.block k := by
    simp only [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx0 | hx1 <;> rcases hy with hy0 | hy1
    · exfalso
      exact hxy (hx0.trans hy0.symm)
    · subst x
      subst y
      rfl
    · subst x
      subst y
      exact Set.pair_comm _ _
    · exfalso
      exact hxy (hx1.trans hy1.symm)
  rcases hq₀rg with hq₀L | hq₀R
  · rcases hq₁rg with hq₁L | hq₁R
    · have hpair := hpair_eq_of_mem i hqne hq₀L hq₁L
      exact (hcross.2.2.1 (hQ.trans (by simpa [i] using hpair))).elim
    · exact ⟨q₀, q₁, by simpa [i] using hq₀L, by simpa [j] using hq₁R, hQ⟩
  · rcases hq₁rg with hq₁L | hq₁R
    · refine ⟨q₁, q₀, by simpa [i] using hq₁L, by simpa [j] using hq₀R, ?_⟩
      simpa [Set.pair_comm] using hQ
    · have hpair := hpair_eq_of_mem j hqne hq₀R hq₁R
      exact (hcross.2.2.2 (hQ.trans (by simpa [j] using hpair))).elim

/-- A cross common base gives an actual edge in the repaired admissible
pair-cycle graph via the canonical common-base target. -/
theorem repairMove_of_crossCommonBase
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (s : Fin N) {Q : Set α} (hcross : IsCrossCommonBase A s Q) :
    RepairMove h2N A
      (commonBaseRepairTarget A h2N s hcross.1 hcross.2.1) := by
  exact repairMove_commonBaseRepairTarget A h2N s hcross.1 hcross.2.1

/-- A wholesale-swap common base likewise gives a legal repair-graph edge. -/
theorem repairMove_of_swapCommonBase
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (s : Fin N) {Q : Set α} (hswap : IsSwapCommonBase A s Q) :
    RepairMove h2N A
      (commonBaseRepairTarget A h2N s hswap.1 hswap.2.1) := by
  exact repairMove_commonBaseRepairTarget A h2N s hswap.1 hswap.2.1

/-- Global low-potential consequence in the new repair language.  Whenever
`closurePotential A < N`, the Sprint 3 rigidity theorem guarantees a
nontrivial common base somewhere; that repair is therefore either cross or a
wholesale swap. -/
theorem exists_cross_or_swap_common_base_of_closurePotential_lt_card
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (hlt : closurePotential A < N) :
    ∃ s : Fin N, ∃ Q : Set α,
      IsCrossCommonBase A s Q ∨ IsSwapCommonBase A s Q := by
  obtain ⟨s, Q, hL, hR, hne⟩ :=
    exists_alternative_repartition_of_closurePotential_lt_card A h2N hlt
  exact ⟨s, Q, alternative_common_base_cross_or_swap A s hL hR hne⟩

/-- Cross-base relation of the left boundary minor between the two old repair
blocks. -/
def leftBoundaryCrossRelation
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) :
    BinaryRelationCycle.Relation :=
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  PairCycle.crossBaseRelation (leftRepairMinor A s)
    (A.element i false) (A.element i true)
    (A.element j false) (A.element j true)

/-- Cross-base relation of the dual right boundary minor on the same four
moved elements. -/
def dualRightBoundaryCrossRelation
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N) :
    BinaryRelationCycle.Relation :=
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  PairCycle.crossBaseRelation ((rightRepairMinor A s)✶)
    (A.element i false) (A.element i true)
    (A.element j false) (A.element j true)

/-- If the old right block itself is a common base, then both boundary
cross-relations have full support: in each boundary matroid both old pair
blocks are bases. -/
theorem boundary_crossRelations_fullSupport_of_swapCommonBase
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (s : Fin N) {Q : Set α} (hswap : IsSwapCommonBase A s Q) :
    BinaryRelationCycle.FullSupport (leftBoundaryCrossRelation A s) ∧
    BinaryRelationCycle.FullSupport (dualRightBoundaryCrossRelation A s) := by
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  have hdis : Disjoint
      ({A.element i false, A.element i true} : Set α)
      ({A.element j false, A.element j true} : Set α) := by
    simpa [i, j, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      modified_blocks_disjoint A h2N s
  have hLi : (leftRepairMinor A s).IsBase
      ({A.element i false, A.element i true} : Set α) := by
    simpa [i, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      left_block_isBase_leftRepairMinor A h2N s
  have hSi : ((rightRepairMinor A s)✶).IsBase
      ({A.element i false, A.element i true} : Set α) := by
    simpa [i, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      left_block_isBase_dual_rightRepairMinor A h2N s
  have hLjBlock : (leftRepairMinor A s).IsBase (A.block j) := by
    simpa [hswap.2.2] using hswap.1
  have hSjBlock : ((rightRepairMinor A s)✶).IsBase (A.block j) := by
    simpa [hswap.2.2] using hswap.2.1
  have hLj : (leftRepairMinor A s).IsBase
      ({A.element j false, A.element j true} : Set α) := by
    simpa [j, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using hLjBlock
  have hSj : ((rightRepairMinor A s)✶).IsBase
      ({A.element j false, A.element j true} : Set α) := by
    simpa [j, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using hSjBlock
  constructor
  · simpa [leftBoundaryCrossRelation, i, j] using
      PairCycle.crossBaseRelation_fullSupport (leftRepairMinor A s)
        (A.element_ne i) (A.element_ne j) hdis hLi hLj
  · simpa [dualRightBoundaryCrossRelation, i, j] using
      PairCycle.crossBaseRelation_fullSupport ((rightRepairMinor A s)✶)
        (A.element_ne i) (A.element_ne j) hdis hSi hSj

/-- Representation-free description of the exceptional swap-only geometry.
If a boundary admits the wholesale swap and the two boundary matroids have no
common cross cell, then their cross-base patterns are both bijections.  Since
they are pointwise disjoint, they are the two complementary perfect matchings
of the `2 × 2` Boolean grid, exactly as found by the exhaustive four-element
classification. -/
theorem swap_only_crossRelations_are_bijections
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (s : Fin N) {Q : Set α} (hswap : IsSwapCommonBase A s Q)
    (hnoCrossCell : ∀ x y,
      ¬ (leftBoundaryCrossRelation A s x y ∧
        dualRightBoundaryCrossRelation A s x y)) :
    BinaryRelationCycle.BijectionRelation (leftBoundaryCrossRelation A s) ∧
    BinaryRelationCycle.BijectionRelation (dualRightBoundaryCrossRelation A s) := by
  obtain ⟨hLfull, hSfull⟩ :=
    boundary_crossRelations_fullSupport_of_swapCommonBase A h2N s hswap
  exact BinaryRelationCycle.bijectionRelations_of_disjoint_fullSupport
    hLfull hSfull hnoCrossCell

end Rank4GcdTwoRepair
end HigherRankKUM
