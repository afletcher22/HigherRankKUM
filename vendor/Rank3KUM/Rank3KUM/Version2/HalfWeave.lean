import Rank3KUM.HalfWeave.ParallelClasses

namespace Rank3KUM.Version2.HalfWeave

open Set
open Rank3KUM.HalfWeave

noncomputable section

variable {α : Type*}

/--
Version-2 name for the now-core largest-first block hypothesis.  The core
half-weave no longer requires a global nonincreasing ordering of block sizes.
-/
abbrev LargestFirstBlockModel := Rank3KUM.HalfWeave.LargestFirstBlockModel

/-- Every legacy fully sorted model remains a valid largest-first model. -/
def LargestFirstBlockModel.ofSorted
    {k m : ℕ}
    (S : Rank3KUM.HalfWeave.SortedBlockModel k m) :
    LargestFirstBlockModel k m :=
  Rank3KUM.HalfWeave.LargestFirstBlockModel.ofSorted S

/-- The version-2 block-crossing theorem is now the core theorem. -/
theorem woven_successor_blocks_ne
    {k m : ℕ}
    (hk : 0 < k)
    (S : LargestFirstBlockModel k m)
    (p : Fin k × Bool) :
    S.block (halfWeaveEquiv k hk p) ≠
      S.block (halfWeaveEquiv k hk (weaveNext k hk p)) :=
  Rank3KUM.HalfWeave.largestFirst_woven_successor_blocks_ne hk S p

/-- Version-2 name for the core weakened rank-two enumeration interface. -/
abbrev RankTwoLargestFirstEnumeration
    (M : Matroid α) (k m : ℕ) :=
  Rank3KUM.HalfWeave.RankTwoSortedEnumeration M k m

/-- A core rank-two enumeration already satisfies the version-2 interface. -/
def RankTwoLargestFirstEnumeration.ofSorted
    {M : Matroid α} {k m : ℕ}
    (D : Rank3KUM.HalfWeave.RankTwoSortedEnumeration M k m) :
    RankTwoLargestFirstEnumeration M k m := D

/-- Apply the half weave to largest-first block data. -/
def rankTwoWoven
    {M : Matroid α} {k m : ℕ}
    (D : RankTwoLargestFirstEnumeration M k m)
    (hk : 0 < k) :
    Fin k × Bool ≃ M.E :=
  Rank3KUM.HalfWeave.rankTwoWoven D hk

/-- Every woven successor pair is independent. -/
theorem rankTwoWoven_successor_indep
    {M : Matroid α} {k m : ℕ}
    (D : RankTwoLargestFirstEnumeration M k m)
    (hk : 0 < k)
    (p : Fin k × Bool) :
    M.Indep
      ({((rankTwoWoven D hk p : M.E) : α),
        ((rankTwoWoven D hk (weaveNext k hk p) : M.E) : α)} : Set α) := by
  simpa [rankTwoWoven] using
    Rank3KUM.HalfWeave.rankTwoWoven_successor_indep D hk p

/-- Every woven successor pair is a basis in rank two. -/
theorem rankTwoWoven_successor_isBase
    (M : Matroid α)
    {k m : ℕ}
    (D : RankTwoLargestFirstEnumeration M k m)
    (hk : 0 < k)
    (hRank : M.eRank = 2)
    (p : Fin k × Bool) :
    M.IsBase
      ({((rankTwoWoven D hk p : M.E) : α),
        ((rankTwoWoven D hk (weaveNext k hk p) : M.E) : α)} : Set α) := by
  simpa [rankTwoWoven] using
    Rank3KUM.HalfWeave.rankTwoWoven_successor_isBase M D hk hRank p

/-- Clean paper-level output interface, Definition 4.1. -/
structure CyclicRankTwoBasisOrdering
    (M : Matroid α) (k : ℕ) (hk : 0 < k) where
  order : Fin k × Bool ≃ M.E
  adjacent_isBase :
    ∀ p : Fin k × Bool,
      M.IsBase
        ({((order p : M.E) : α),
          ((order (weaveNext k hk p) : M.E) : α)} : Set α)

/-- Largest-first data yields a cyclic rank-two basis ordering. -/
def cyclicRankTwoBasisOrderingOfLargestFirst
    (M : Matroid α)
    {k m : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 2)
    (D : RankTwoLargestFirstEnumeration M k m) :
    CyclicRankTwoBasisOrdering M k hk where
  order := rankTwoWoven D hk
  adjacent_isBase := rankTwoWoven_successor_isBase M D hk hRank

/--
Paper v2, Proposition 4.2.  Kept as a compatibility endpoint; the active core
now supports the weaker largest-first hypothesis directly.
-/
def cyclicRankTwoBasisOrderingOfUniformlyDense
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hk : 0 < k)
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hRank : M.eRank = 2) :
    CyclicRankTwoBasisOrdering M k hk := by
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  let D :=
    Rank3KUM.HalfWeave.rankTwoSortedEnumerationOfUniformlyDense
      M k hcard hDense hLoopless hRank
  exact cyclicRankTwoBasisOrderingOfLargestFirst M hk hRank D

#print axioms Rank3KUM.Version2.HalfWeave.woven_successor_blocks_ne
#print axioms Rank3KUM.Version2.HalfWeave.rankTwoWoven_successor_isBase
#print axioms Rank3KUM.Version2.HalfWeave.cyclicRankTwoBasisOrderingOfUniformlyDense

end

end Rank3KUM.Version2.HalfWeave
