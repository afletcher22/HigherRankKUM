import HigherRankKUM.Rank4.GcdTwoRepairDichotomy
import HigherRankKUM.Rank4.CrossRepartitionParity

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open Set
open PairCycle

variable {α : Type*}

/-- Removing one selected element from each of two disjoint labelled pairs
leaves exactly the two complementary selected elements. -/
private theorem pair_union_sdiff_cross_pair
    {c₀ c₁ d₀ d₁ : α}
    (hc : c₀ ≠ c₁) (hd : d₀ ≠ d₁)
    (hCD : Disjoint ({c₀, c₁} : Set α) ({d₀, d₁} : Set α))
    (u v : Bool) :
    (({c₀, c₁} : Set α) ∪ {d₀, d₁}) \
        {bitPick c₀ c₁ u, bitPick d₀ d₁ v} =
      {bitPick c₀ c₁ (Bool.not u), bitPick d₀ d₁ (Bool.not v)} := by
  have hc0d0 : c₀ ≠ d₀ := by
    intro h
    exact Set.disjoint_left.1 hCD (by simp) (by simpa [h])
  have hc0d1 : c₀ ≠ d₁ := by
    intro h
    exact Set.disjoint_left.1 hCD (by simp) (by simpa [h])
  have hc1d0 : c₁ ≠ d₀ := by
    intro h
    exact Set.disjoint_left.1 hCD (by simp) (by simpa [h])
  have hc1d1 : c₁ ≠ d₁ := by
    intro h
    exact Set.disjoint_left.1 hCD (by simp) (by simpa [h])
  cases u <;> cases v <;>
    ext x <;>
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, bitPick, Bool.not_false, Bool.not_true]
  all_goals aesop

/-- Every genuine cross common base is encoded by two Boolean choices relative
to the existing labels on the two repaired blocks.  Its complementary repaired
block is obtained by negating both choices.

This is the set-level bridge from the abstract repair graph to the generic
six-block cross-repartition parity theorem. -/
theorem crossCommonBase_bit_parameters
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (s : Fin N) {Q : Set α} (hcross : IsCrossCommonBase A s Q) :
    ∃ u v : Bool,
      Q =
        {bitPick
            (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false)
            (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true) u,
         bitPick
            (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false)
            (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true) v} ∧
      repairGround A s \ Q =
        {bitPick
            (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false)
            (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true)
            (Bool.not u),
         bitPick
            (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false)
            (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true)
            (Bool.not v)} := by
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  obtain ⟨x, y, hx, hy, hQ⟩ :=
    crossCommonBase_eq_pair_one_from_each A h2N s hcross
  have hxbit : ∃ u : Bool,
      x = bitPick (A.element i false) (A.element i true) u := by
    simp only [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · exact ⟨false, by simpa [bitPick] using hx⟩
    · exact ⟨true, by simpa [bitPick] using hx⟩
  have hybit : ∃ v : Bool,
      y = bitPick (A.element j false) (A.element j true) v := by
    simp only [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · exact ⟨false, by simpa [bitPick] using hy⟩
    · exact ⟨true, by simpa [bitPick] using hy⟩
  obtain ⟨u, rfl⟩ := hxbit
  obtain ⟨v, rfl⟩ := hybit
  refine ⟨u, v, ?_, ?_⟩
  · simpa [i, j] using hQ
  · rw [hQ]
    have hdis : Disjoint
        ({A.element i false, A.element i true} : Set α)
        ({A.element j false, A.element j true} : Set α) := by
      simpa [i, j, AdmissiblePairCycle.Data.block,
        AdmissiblePairCycle.pairSet] using modified_blocks_disjoint A h2N s
    have hcomp := pair_union_sdiff_cross_pair
      (A.element_ne i) (A.element_ne j) hdis u v
    simpa [repairGround, i, j, AdmissiblePairCycle.Data.block,
      AdmissiblePairCycle.pairSet] using hcomp

end Rank4GcdTwoRepair
end HigherRankKUM
