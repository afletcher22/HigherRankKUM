import HigherRankKUM.Rank4.ThreePairDual
import HigherRankKUM.Rank4.ThreePairDualBase

namespace HigherRankKUM
namespace Rank4ThreePairDual

open Set
open BinaryRelationCycle
open PairCycle

variable {α : Type*}

private lemma bitPick_mem_pair (x₀ x₁ : α) (b : Bool) :
    bitPick x₀ x₁ b ∈ ({x₀, x₁} : Set α) := by
  cases b <;> simp [bitPick]

/-- A rank-four middle-pair relation is exactly the endpoint cross-base
relation after contracting the middle pair.  This is the contraction-side
translation used by the wholesale-swap parity argument. -/
theorem middlePairRelation_eq_contract_crossBaseRelation
    (M : Matroid α) {x₀ x₁ y₀ y₁ z₀ z₁ : α}
    (hY : M.Indep ({y₀, y₁} : Set α))
    (hXY : Disjoint ({x₀, x₁} : Set α) ({y₀, y₁} : Set α))
    (hYZ : Disjoint ({y₀, y₁} : Set α) ({z₀, z₁} : Set α)) :
    middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁ =
      crossBaseRelation (M.contract ({y₀, y₁} : Set α)) x₀ x₁ z₀ z₁ := by
  have hEndpoints : ∀ x z,
      Disjoint
        ({bitPick x₀ x₁ x, bitPick z₀ z₁ z} : Set α)
        ({y₀, y₁} : Set α) := by
    intro x z
    rw [Set.disjoint_left]
    intro e he heYmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with h | h
    · subst e
      exact Set.disjoint_left.1 hXY (bitPick_mem_pair x₀ x₁ x) heYmem
    · subst e
      exact Set.disjoint_left.1 hYZ heYmem (bitPick_mem_pair z₀ z₁ z)
  funext x z
  apply propext
  have hshift := PairCycle.shifted_window_iff_crossBaseRelation
    M hY hEndpoints x z
  have hset :
      ({bitPick x₀ x₁ x, bitPick z₀ z₁ z} : Set α) ∪ {y₀, y₁} =
        {bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z} := by
    ext e
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  change M.IsBase
      ({bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z} : Set α) ↔
    crossBaseRelation (M.contract ({y₀, y₁} : Set α)) x₀ x₁ z₀ z₁ x z
  rw [← hset]
  exact hshift

/-- Contraction-side rank-four triangle obstruction.

If `A ∪ B`, `C ∪ B`, and `D ∪ B` are bases, then after contracting the
middle pair `B`, the endpoint pairs `A,C,D` are rank-two bases.  Hence two
forced middle-pair relations around `A-C-D` obstruct the cyclic triple.
This is the outer-triangle ingredient in the wholesale-swap proof. -/
theorem middlePairRelation_contract_triangle_not_cyclicSatisfiable
    (M : Matroid α)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : α}
    (ha : a₀ ≠ a₁) (hc : c₀ ≠ c₁) (hd : d₀ ≠ d₁)
    (hAB : Disjoint ({a₀, a₁} : Set α) ({b₀, b₁} : Set α))
    (hCB : Disjoint ({c₀, c₁} : Set α) ({b₀, b₁} : Set α))
    (hDB : Disjoint ({d₀, d₁} : Set α) ({b₀, b₁} : Set α))
    (hAC : Disjoint ({a₀, a₁} : Set α) ({c₀, c₁} : Set α))
    (hCD : Disjoint ({c₀, c₁} : Set α) ({d₀, d₁} : Set α))
    (hAD : Disjoint ({a₀, a₁} : Set α) ({d₀, d₁} : Set α))
    (hABbase : M.IsBase (({a₀, a₁} : Set α) ∪ {b₀, b₁}))
    (hCBbase : M.IsBase (({c₀, c₁} : Set α) ∪ {b₀, b₁}))
    (hDBbase : M.IsBase (({d₀, d₁} : Set α) ∪ {b₀, b₁}))
    (hABC : BijectionRelation (middlePairRelation M a₀ a₁ b₀ b₁ c₀ c₁))
    (hCBD : BijectionRelation (middlePairRelation M c₀ c₁ b₀ b₁ d₀ d₁)) :
    ¬ CyclicSatisfiable
      [middlePairRelation M a₀ a₁ b₀ b₁ c₀ c₁,
       middlePairRelation M c₀ c₁ b₀ b₁ d₀ d₁,
       middlePairRelation M d₀ d₁ b₀ b₁ a₀ a₁] := by
  let B : Set α := {b₀, b₁}
  let N : Matroid α := M.contract B
  have hBind : M.Indep B := by
    apply hABbase.indep.subset
    intro e he
    exact Or.inr (by simpa [B] using he)
  have hAbase : N.IsBase ({a₀, a₁} : Set α) := by
    dsimp [N]
    exact hBind.contract_isBase_iff.2 ⟨hABbase, by simpa [B] using hAB⟩
  have hCbase : N.IsBase ({c₀, c₁} : Set α) := by
    dsimp [N]
    exact hBind.contract_isBase_iff.2 ⟨hCBbase, by simpa [B] using hCB⟩
  have hDbase : N.IsBase ({d₀, d₁} : Set α) := by
    dsimp [N]
    exact hBind.contract_isBase_iff.2 ⟨hDBbase, by simpa [B] using hDB⟩

  have hR₁ :
      middlePairRelation M a₀ a₁ b₀ b₁ c₀ c₁ =
        crossBaseRelation N a₀ a₁ c₀ c₁ := by
    simpa [N, B] using
      (middlePairRelation_eq_contract_crossBaseRelation M hBind hAB hCB.symm)
  have hR₂ :
      middlePairRelation M c₀ c₁ b₀ b₁ d₀ d₁ =
        crossBaseRelation N c₀ c₁ d₀ d₁ := by
    simpa [N, B] using
      (middlePairRelation_eq_contract_crossBaseRelation M hBind hCB hDB.symm)
  have hR₃ :
      middlePairRelation M d₀ d₁ b₀ b₁ a₀ a₁ =
        crossBaseRelation N d₀ d₁ a₀ a₁ := by
    simpa [N, B] using
      (middlePairRelation_eq_contract_crossBaseRelation M hBind hDB hAB.symm)

  have hACbij : BijectionRelation (crossBaseRelation N a₀ a₁ c₀ c₁) := by
    rw [hR₁] at hABC
    exact hABC
  have hCDbij : BijectionRelation (crossBaseRelation N c₀ c₁ d₀ d₁) := by
    rw [hR₂] at hCBD
    exact hCBD
  have htri : ¬ CyclicSatisfiable
      [crossBaseRelation N a₀ a₁ c₀ c₁,
       crossBaseRelation N c₀ c₁ d₀ d₁,
       crossBaseRelation N d₀ d₁ a₀ a₁] :=
    PairCycle.crossBaseRelation_triangle_not_cyclicSatisfiable
      N ha hc hd hAC hCD hAD hAbase hCbase hDbase hACbij hCDbij

  intro hcyc
  rw [hR₁, hR₂, hR₃] at hcyc
  exact htri hcyc

/-- Six-element representation-free rank-four triangle obstruction.

Let `X,Y,Z` be three pairwise-disjoint two-element blocks such that each
pairwise union is a basis of `M`.  If the first two cyclic middle-pair
relations are forced, then the three-relation cycle cannot be satisfied.

The proof restricts to `X ∪ Y ∪ Z`, dualizes to rank two, translates each
middle-pair relation to the complementary endpoint cross relation, and then
applies the intrinsic rank-two triangle obstruction.  No representability
or field hypothesis is used. -/
theorem middlePairRelation_triangle_not_cyclicSatisfiable
    (M : Matroid α) {x₀ x₁ y₀ y₁ z₀ z₁ : α}
    (hx : x₀ ≠ x₁) (hy : y₀ ≠ y₁) (hz : z₀ ≠ z₁)
    (hXY : Disjoint ({x₀, x₁} : Set α) ({y₀, y₁} : Set α))
    (hYZ : Disjoint ({y₀, y₁} : Set α) ({z₀, z₁} : Set α))
    (hXZ : Disjoint ({x₀, x₁} : Set α) ({z₀, z₁} : Set α))
    (hXYbase : M.IsBase (({x₀, x₁} : Set α) ∪ {y₀, y₁}))
    (hYZbase : M.IsBase (({y₀, y₁} : Set α) ∪ {z₀, z₁}))
    (hXZbase : M.IsBase (({x₀, x₁} : Set α) ∪ {z₀, z₁}))
    (hXYZ : BijectionRelation (middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁))
    (hZXY : BijectionRelation (middlePairRelation M z₀ z₁ x₀ x₁ y₀ y₁)) :
    ¬ CyclicSatisfiable
      [middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁,
       middlePairRelation M z₀ z₁ x₀ x₁ y₀ y₁,
       middlePairRelation M y₀ y₁ z₀ z₁ x₀ x₁] := by
  let X : Set α := {x₀, x₁}
  let Y : Set α := {y₀, y₁}
  let Z : Set α := {z₀, z₁}
  let U : Set α := X ∪ Y ∪ Z
  let N : Matroid α := (M.restrict U)✶

  have hXYsub : X ∪ Y ⊆ U := by
    intro e he
    exact Or.inl he
  have hUground : U ⊆ M.E := by
    intro e he
    rcases he with heXY | heZ
    · exact hXYbase.subset_ground (by simpa [X, Y] using heXY)
    · exact hXZbase.subset_ground (by
        have : e ∈ X ∪ Z := Or.inr heZ
        simpa [X, Z] using this)
  have hUspan : M.Spanning U := by
    apply hXYbase.spanning_of_superset
    · simpa [X, Y] using hXYsub
    · exact hUground

  have hXbase : N.IsBase X := by
    have h := dual_restrict_pair_isBase M hXY hXZ
      (by simpa [U, X, Y, Z] using hUspan)
      (by simpa [Y, Z] using hYZbase)
    simpa [N, U, X, Y, Z] using h
  have hYbase : N.IsBase Y := by
    have h := dual_restrict_pair_isBase M hXY.symm hYZ
      (by
        simpa [U, X, Y, Z, Set.union_assoc, Set.union_left_comm, Set.union_comm]
          using hUspan)
      (by simpa [X, Z] using hXZbase)
    simpa [N, U, X, Y, Z, Set.union_assoc, Set.union_left_comm, Set.union_comm] using h
  have hZbase : N.IsBase Z := by
    have h := dual_restrict_pair_isBase M hXZ.symm hYZ.symm
      (by
        simpa [U, X, Y, Z, Set.union_assoc, Set.union_left_comm, Set.union_comm]
          using hUspan)
      (by simpa [X, Y] using hXYbase)
    simpa [N, U, X, Y, Z, Set.union_assoc, Set.union_left_comm, Set.union_comm] using h

  have hR₁ :
      middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁ =
        doubleRelabel (crossBaseRelation N x₀ x₁ z₀ z₁) := by
    simpa [N, U, X, Y, Z] using
      (middlePairRelation_eq_dual_crossBaseRelation M hx hy hz
        hXY hYZ hXZ hXYbase hYZbase hXZbase)
  have hR₂ :
      middlePairRelation M z₀ z₁ x₀ x₁ y₀ y₁ =
        doubleRelabel (crossBaseRelation N z₀ z₁ y₀ y₁) := by
    have h := middlePairRelation_eq_dual_crossBaseRelation M hz hx hy
      hXZ.symm hXY hYZ.symm
      (by simpa [Set.union_comm] using hXZbase)
      hXYbase
      (by simpa [Set.union_comm] using hYZbase)
    simpa [N, U, X, Y, Z, Set.union_assoc, Set.union_left_comm, Set.union_comm] using h
  have hR₃ :
      middlePairRelation M y₀ y₁ z₀ z₁ x₀ x₁ =
        doubleRelabel (crossBaseRelation N y₀ y₁ x₀ x₁) := by
    have h := middlePairRelation_eq_dual_crossBaseRelation M hy hz hx
      hYZ hXZ.symm hXY.symm
      hYZbase
      (by simpa [Set.union_comm] using hXZbase)
      (by simpa [Set.union_comm] using hXYbase)
    simpa [N, U, X, Y, Z, Set.union_assoc, Set.union_left_comm, Set.union_comm] using h

  have hXZbij : BijectionRelation (crossBaseRelation N x₀ x₁ z₀ z₁) := by
    rw [hR₁] at hXYZ
    exact doubleRelabel_bijection_iff.mp hXYZ
  have hZYbij : BijectionRelation (crossBaseRelation N z₀ z₁ y₀ y₁) := by
    rw [hR₂] at hZXY
    exact doubleRelabel_bijection_iff.mp hZXY
  have htri : ¬ CyclicSatisfiable
      [crossBaseRelation N x₀ x₁ z₀ z₁,
       crossBaseRelation N z₀ z₁ y₀ y₁,
       crossBaseRelation N y₀ y₁ x₀ x₁] :=
    PairCycle.crossBaseRelation_triangle_not_cyclicSatisfiable
      N hx hz hy hXZ hYZ.symm hXY hXbase hZbase hYbase hXZbij hZYbij

  intro hcyc
  rw [hR₁, hR₂, hR₃] at hcyc
  exact htri ((cyclicSatisfiable_three_doubleRelabel _ _ _).mp hcyc)

end Rank4ThreePairDual
end HigherRankKUM
