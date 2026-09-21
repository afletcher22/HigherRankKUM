import Rank3KUM.HalfWeave.FinitePartitionLargestFirst
import Rank3KUM.HalfWeave.ParallelClasses

namespace Rank3KUM.HalfWeave

open Set

noncomputable section

variable {α : Type*}

/--
Uniform density in rank two directly yields the only output needed by the
tight-set branches: a cyclic enumeration whose woven successor pairs are
bases.  The enumeration bookkeeping is supplied by the generic finite-
partition construction; the matroid-specific work is only the parallel-class
partition, its size bound, and the cross-class basis argument.
-/
theorem exists_cyclic_adjacent_base_order_of_uniformlyDense_direct
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hk : 0 < k)
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hRank : M.eRank = 2) :
    ∃ order : Fin k × Bool ≃ M.E,
      ∀ p : Fin k × Bool,
        M.IsBase
          ({((order p : M.E) : α),
            ((order (weaveNext k hk p) : M.E) : α)} : Set α) := by
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  have hbound :
      ∀ q : (closureFinpartition M).parts, q.1.card ≤ k := by
    intro q
    exact
      card_closureFinpartition_part_le
        M k hDense hLoopless q.1 q.2
  obtain ⟨y, S, hclassify⟩ :=
    FinitePartition.exists_largestFirst_enumeration
      (closureFinpartition M) k hk hcard hbound
  let order : Fin k × Bool ≃ M.E := woven k hk y
  refine ⟨order, ?_⟩
  intro p
  let a : Fin (2 * k) := halfWeaveEquiv k hk p
  let b : Fin (2 * k) :=
    halfWeaveEquiv k hk (weaveNext k hk p)
  have hblocks : S.block a ≠ S.block b := by
    simpa [a, b] using
      (largestFirst_woven_successor_blocks_ne hk S p)
  have hclosure :
      M.closure ({((y a : M.E) : α)} : Set α) ≠
        M.closure ({((y b : M.E) : α)} : Set α) := by
    intro hcl
    apply hblocks
    apply (hclassify a b).2
    have hmem :
        y b ∈ (closureFinpartition M).part (y a) :=
      (mem_closureFinpartition_part_iff M (y a) (y b)).2 hcl
    have hpartMem :
        (closureFinpartition M).part (y a) ∈
          (closureFinpartition M).parts :=
      (closureFinpartition M).part_mem.2 (Finset.mem_univ _)
    have hrev :
        (closureFinpartition M).part (y b) =
          (closureFinpartition M).part (y a) :=
      ((closureFinpartition M).part_eq_iff_mem hpartMem).2 hmem
    exact hrev.symm
  have hab : a ≠ b := by
    intro hab
    apply hblocks
    exact congrArg S.block hab
  have hyne : y a ≠ y b := by
    intro hy
    exact hab (y.injective hy)
  have hne :
      ((y a : M.E) : α) ≠ ((y b : M.E) : α) := by
    intro hcoe
    apply hyne
    exact Subtype.ext hcoe
  have hindep :
      M.Indep
        ({((y a : M.E) : α),
          ((y b : M.E) : α)} : Set α) :=
    pair_indep_of_closure_ne
      M hLoopless (y a).property (y b).property hclosure
  have hbase :
      M.IsBase
        ({((y a : M.E) : α),
          ((y b : M.E) : α)} : Set α) :=
    pair_isBase_of_indep_of_eRank_eq_two M hRank hne hindep
  simpa [order, woven, a, b] using hbase

#print axioms Rank3KUM.HalfWeave.exists_cyclic_adjacent_base_order_of_uniformlyDense_direct

end

end Rank3KUM.HalfWeave
