import Rank3KUM.HalfWeave.LargestFirst
import Mathlib.Combinatorics.Matroid.Rank.ENat

namespace Rank3KUM.HalfWeave

/-- A finite independent pair of distinct elements is a base in rank two. -/
theorem pair_isBase_of_indep_of_eRank_eq_two
    {α : Type*}
    (M : Matroid α)
    (hRank : M.eRank = 2)
    {e f : α}
    (hef : e ≠ f)
    (hpair : M.Indep ({e, f} : Set α)) :
    M.IsBase ({e, f} : Set α) := by
  apply hpair.isBase_of_eRk_ge (Set.toFinite {e, f})
  rw [hRank, hpair.eRk_eq_encard, Set.encard_pair hef]

/--
Data needed to apply the rank-two half-weave theorem to a matroid.
The block model only requires a largest first block; the remaining blocks
need not be globally sorted by size.
-/
structure RankTwoSortedEnumeration
    {α : Type*}
    (M : Matroid α)
    (k m : ℕ) where
  y : Fin (2 * k) ≃ M.E
  sortedBlocks : LargestFirstBlockModel k m
  indep_of_blocks_ne :
    ∀ a b : Fin (2 * k),
      sortedBlocks.block a ≠ sortedBlocks.block b →
        M.Indep
          ({((y a : M.E) : α),
            ((y b : M.E) : α)} : Set α)

/--
In a loopless matroid, elements in different singleton-closure classes form
an independent pair.
-/
theorem pair_indep_of_closure_ne
    {α : Type*}
    (M : Matroid α)
    (hLoopless : M.Loopless)
    {e f : α}
    (he : e ∈ M.E)
    (hf : f ∈ M.E)
    (hclosure :
      M.closure ({e} : Set α) ≠
        M.closure ({f} : Set α)) :
    M.Indep ({e, f} : Set α) := by
  let : M.Loopless := hLoopless
  have heNonloop : M.IsNonloop e :=
    Matroid.isNonloop_of_loopless he
  have hfNonloop : M.IsNonloop f :=
    Matroid.isNonloop_of_loopless hf
  by_contra hdep
  apply hclosure
  exact
    (heNonloop.closure_eq_closure_iff_eq_or_dep
      hfNonloop).2 (Or.inr hdep)

/-- A rank-two matroid has two ground elements in different singleton-closure classes. -/
theorem exists_pair_closure_ne_of_eRank_eq_two
    {α : Type*}
    (M : Matroid α)
    (hRank : M.eRank = 2) :
    ∃ e f : α,
      e ∈ M.E ∧ f ∈ M.E ∧
        M.closure ({e} : Set α) ≠
          M.closure ({f} : Set α) := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hBcard : B.encard = 2 := by
    rw [hB.encard_eq_eRank, hRank]
  obtain ⟨e, f, hef, rfl⟩ :=
    Set.encard_eq_two.mp hBcard
  have heE : e ∈ M.E :=
    hB.subset_ground (by simp)
  have hfE : f ∈ M.E :=
    hB.subset_ground (by simp)
  refine ⟨e, f, heE, hfE, ?_⟩
  intro hclosure
  have heNonloop : M.IsNonloop e :=
    hB.indep.isNonloop_of_mem (by simp)
  have hfNonloop : M.IsNonloop f :=
    hB.indep.isNonloop_of_mem (by simp)
  rcases
      (heNonloop.closure_eq_closure_iff_eq_or_dep
        hfNonloop).1 hclosure with heq | hdep
  · exact hef heq
  · exact hdep hB.indep

#print axioms Rank3KUM.HalfWeave.exists_pair_closure_ne_of_eRank_eq_two

/--
A legacy fully sorted block model can still construct the now-weaker
rank-two enumeration interface.
-/
def RankTwoSortedEnumeration.ofClosureBlocks
    {α : Type*}
    (M : Matroid α)
    {k m : ℕ}
    (hLoopless : M.Loopless)
    (y : Fin (2 * k) ≃ M.E)
    (S : SortedBlockModel k m)
    (hblock :
      ∀ a b : Fin (2 * k),
        S.block a = S.block b ↔
          M.closure
              ({((y a : M.E) : α)} : Set α) =
            M.closure
              ({((y b : M.E) : α)} : Set α)) :
    RankTwoSortedEnumeration M k m where
  y := y
  sortedBlocks := LargestFirstBlockModel.ofSorted S
  indep_of_blocks_ne := by
    intro a b hab
    apply pair_indep_of_closure_ne
      M hLoopless (y a).property (y b).property
    intro hclosure
    exact hab ((hblock a b).2 hclosure)

#print axioms Rank3KUM.HalfWeave.pair_indep_of_closure_ne
#print axioms Rank3KUM.HalfWeave.RankTwoSortedEnumeration.ofClosureBlocks

/-- The ground-set enumeration obtained by applying the half weave. -/
def rankTwoWoven
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k) :
    Fin k × Bool ≃ M.E :=
  woven k hk D.y

@[simp] theorem rankTwoWoven_false
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (i : Fin k) :
    rankTwoWoven D hk (i, false) =
      D.y (firstIndex k i) := by
  simp [rankTwoWoven]

@[simp] theorem rankTwoWoven_true
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (i : Fin k) :
    rankTwoWoven D hk (i, true) =
      D.y (secondIndex k i) := by
  simp [rankTwoWoven]

/-- Successive woven values are distinct in the ground-set subtype. -/
theorem rankTwoWoven_successor_ne
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (p : Fin k × Bool) :
    rankTwoWoven D hk p ≠
      rankTwoWoven D hk (weaveNext k hk p) := by
  have hblocks :=
    largestFirst_woven_successor_blocks_ne hk D.sortedBlocks p
  intro heq
  apply hblocks
  have hindices :
      halfWeaveEquiv k hk p =
        halfWeaveEquiv k hk (weaveNext k hk p) := by
    apply D.y.injective
    simpa [rankTwoWoven, woven] using heq
  exact congrArg D.sortedBlocks.block hindices

/-- Successive woven values remain distinct after coercion to `α`. -/
theorem rankTwoWoven_successor_coe_ne
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (p : Fin k × Bool) :
    ((rankTwoWoven D hk p : M.E) : α) ≠
      ((rankTwoWoven D hk (weaveNext k hk p) : M.E) : α) := by
  intro heq
  apply rankTwoWoven_successor_ne D hk p
  apply Subtype.ext
  exact heq

/-- Every successor pair in the woven enumeration is independent. -/
theorem rankTwoWoven_successor_indep
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (p : Fin k × Bool) :
    M.Indep
      ({((rankTwoWoven D hk p : M.E) : α),
        ((rankTwoWoven D hk
          (weaveNext k hk p) : M.E) : α)} : Set α) := by
  have hblocks :=
    largestFirst_woven_successor_blocks_ne hk D.sortedBlocks p
  simpa [rankTwoWoven, woven] using
    D.indep_of_blocks_ne
      (halfWeaveEquiv k hk p)
      (halfWeaveEquiv k hk (weaveNext k hk p))
      hblocks

/-- In rank two, every woven successor pair is a base. -/
theorem rankTwoWoven_successor_isBase
    {α : Type*}
    (M : Matroid α)
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (hRank : M.eRank = 2)
    (p : Fin k × Bool) :
    M.IsBase
      ({((rankTwoWoven D hk p : M.E) : α),
        ((rankTwoWoven D hk
          (weaveNext k hk p) : M.E) : α)} : Set α) := by
  exact pair_isBase_of_indep_of_eRank_eq_two
    M hRank
    (rankTwoWoven_successor_coe_ne D hk p)
    (rankTwoWoven_successor_indep D hk p)

/--
A supplied largest-first block enumeration produces a cyclic ground-set
enumeration whose every successor pair is a base.
-/
theorem exists_cyclic_adjacent_base_order_of_sortedEnumeration
    {α : Type*}
    (M : Matroid α)
    {k m : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 2)
    (D : RankTwoSortedEnumeration M k m) :
    ∃ order : Fin k × Bool ≃ M.E,
      ∀ p : Fin k × Bool,
        M.IsBase
          ({((order p : M.E) : α),
            ((order (weaveNext k hk p) : M.E) : α)} : Set α) := by
  refine ⟨rankTwoWoven D hk, ?_⟩
  intro p
  exact rankTwoWoven_successor_isBase M D hk hRank p

end Rank3KUM.HalfWeave
