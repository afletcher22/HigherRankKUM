import HigherRankKUM.PairCycle
import HigherRankKUM.FundamentalCircuitExchange

namespace HigherRankKUM
namespace PairCycle

open Set

variable {α : Type*}

/-- For two disjoint labelled two-element bases, an endpoint compatibility
cell is exactly fundamental-circuit membership for the element of the first
base that gets replaced.

This is the representation-free bridge from the Boolean relation language of
pair cycles to ordinary matroid circuit structure. -/
theorem crossBaseRelation_iff_mem_fundCircuit
    (N : Matroid α) {a₀ a₁ b₀ b₁ : α}
    (ha : a₀ ≠ a₁)
    (hAB : Disjoint ({a₀, a₁} : Set α) ({b₀, b₁} : Set α))
    (hA : N.IsBase ({a₀, a₁} : Set α))
    (hB : N.IsBase ({b₀, b₁} : Set α))
    (x y : Bool) :
    crossBaseRelation N a₀ a₁ b₀ b₁ x y ↔
      bitPick a₀ a₁ (Bool.not x) ∈
        N.fundCircuit (bitPick b₀ b₁ y) ({a₀, a₁} : Set α) := by
  have hb₀E : b₀ ∈ N.E := hB.subset_ground (by simp)
  have hb₁E : b₁ ∈ N.E := hB.subset_ground (by simp)
  have hb₀A : b₀ ∉ ({a₀, a₁} : Set α) := by
    intro hb
    exact Set.disjoint_left.1 hAB hb (by simp)
  have hb₁A : b₁ ∉ ({a₀, a₁} : Set α) := by
    intro hb
    exact Set.disjoint_left.1 hAB hb (by simp)
  cases x <;> cases y
  · have h := hA.mem_fundCircuit_iff_exchange_isBase hb₀E hb₀A (show a₁ ∈ ({a₀, a₁} : Set α) by simp)
    rw [crossBaseRelation, bitPick]
    simpa [ha] using h.symm
  · have h := hA.mem_fundCircuit_iff_exchange_isBase hb₁E hb₁A (show a₁ ∈ ({a₀, a₁} : Set α) by simp)
    rw [crossBaseRelation, bitPick]
    simpa [ha] using h.symm
  · have h := hA.mem_fundCircuit_iff_exchange_isBase hb₀E hb₀A (show a₀ ∈ ({a₀, a₁} : Set α) by simp)
    rw [crossBaseRelation, bitPick]
    simpa [ha, Set.pair_comm] using h.symm
  · have h := hA.mem_fundCircuit_iff_exchange_isBase hb₁E hb₁A (show a₀ ∈ ({a₀, a₁} : Set α) by simp)
    rw [crossBaseRelation, bitPick]
    simpa [ha, Set.pair_comm] using h.symm

end PairCycle
end HigherRankKUM
