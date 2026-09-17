import HigherRankKUM.PairCycle
import HigherRankKUM.FundamentalCircuitExchange
import HigherRankKUM.BinaryRelationParity

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
  · have h := HigherRankKUM.Matroid.IsBase.mem_fundCircuit_iff_exchange_isBase
      hA hb₀E hb₀A (show a₁ ∈ ({a₀, a₁} : Set α) by simp)
    rw [crossBaseRelation, bitPick]
    simpa [ha] using h.symm
  · have h := HigherRankKUM.Matroid.IsBase.mem_fundCircuit_iff_exchange_isBase
      hA hb₁E hb₁A (show a₁ ∈ ({a₀, a₁} : Set α) by simp)
    rw [crossBaseRelation, bitPick]
    simpa [ha] using h.symm
  · have h := HigherRankKUM.Matroid.IsBase.mem_fundCircuit_iff_exchange_isBase
      hA hb₀E hb₀A (show a₀ ∈ ({a₀, a₁} : Set α) by simp)
    rw [crossBaseRelation, bitPick]
    simpa [ha, Set.pair_comm] using h.symm
  · have h := HigherRankKUM.Matroid.IsBase.mem_fundCircuit_iff_exchange_isBase
      hA hb₁E hb₁A (show a₀ ∈ ({a₀, a₁} : Set α) by simp)
    rw [crossBaseRelation, bitPick]
    simpa [ha, Set.pair_comm] using h.symm

/-- Once the two-state cross relation is forced, its entire identity-versus-
flip orientation is encoded by a single fundamental-circuit incidence.

With the chosen labelling, the relation is the identity exactly when `a₁`
lies in the fundamental circuit of `b₀` over the basis `{a₀,a₁}`.  Thus a
forced parity obstruction can be rewritten as an XOR of ordinary circuit
membership bits. -/
theorem crossBaseRelation_eq_idRel_iff_mem_fundCircuit
    (N : Matroid α) {a₀ a₁ b₀ b₁ : α}
    (ha : a₀ ≠ a₁)
    (hAB : Disjoint ({a₀, a₁} : Set α) ({b₀, b₁} : Set α))
    (hA : N.IsBase ({a₀, a₁} : Set α))
    (hB : N.IsBase ({b₀, b₁} : Set α))
    (hbij : BinaryRelationCycle.BijectionRelation
      (crossBaseRelation N a₀ a₁ b₀ b₁)) :
    crossBaseRelation N a₀ a₁ b₀ b₁ = BinaryRelationCycle.idRel ↔
      a₁ ∈ N.fundCircuit b₀ ({a₀, a₁} : Set α) := by
  have hcell := crossBaseRelation_iff_mem_fundCircuit
    N ha hAB hA hB false false
  constructor
  · intro hR
    apply hcell.mp
    rw [hR]
    rfl
  · intro hmem
    rcases BinaryRelationCycle.eq_idRel_or_eq_flipRel_of_bijection hbij with hid | hflip
    · exact hid
    · exfalso
      have hff : crossBaseRelation N a₀ a₁ b₀ b₁ false false := hcell.mpr hmem
      rw [hflip] at hff
      simpa [BinaryRelationCycle.flipRel] using hff

end PairCycle
end HigherRankKUM
