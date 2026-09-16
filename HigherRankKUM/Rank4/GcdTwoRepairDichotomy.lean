import HigherRankKUM.Rank4.GcdTwoRepairMove

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

end Rank4GcdTwoRepair
end HigherRankKUM
