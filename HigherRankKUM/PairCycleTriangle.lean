import HigherRankKUM.AdjacentRepair
import HigherRankKUM.BinaryRelationParity

namespace HigherRankKUM
namespace PairCycle

open Set
open BinaryRelationCycle

variable {α : Type*}

private lemma bitPick_mem_pair (x₀ x₁ : α) (b : Bool) :
    bitPick x₀ x₁ b ∈ ({x₀, x₁} : Set α) := by
  cases b <;> simp [bitPick]

private lemma bitPick_ne_of_disjoint
    {a₀ a₁ b₀ b₁ : α}
    (hAB : Disjoint ({a₀, a₁} : Set α) ({b₀, b₁} : Set α))
    (x y : Bool) :
    bitPick a₀ a₁ x ≠ bitPick b₀ b₁ y := by
  intro hEq
  apply Set.disjoint_left.1 hAB (bitPick_mem_pair a₀ a₁ x)
  rw [hEq]
  exact bitPick_mem_pair b₀ b₁ y

/-- Rank-two triangle obstruction for pair-cycle relations.

Let `A`, `B`, and `C` be three pairwise-disjoint labelled two-element bases
of the same matroid. If the cross-base relations `A -> B` and `B -> C` are
forced Boolean bijections, then an allowed `A -> B -> C` path can never close
with a `C -> A` basis edge.

The proof is representation-free.  The unused partner of `B` is parallel to
the selected element of `A` (because the first relation is forced), and also
parallel to the selected element of `C` (because the second relation is
forced). Parallelism is transitive, so the selected `A` and `C` elements are
independent only if they coincide; pairwise disjointness rules that out. -/
theorem crossBaseRelation_triangle_not_cyclicSatisfiable
    (N : Matroid α) {a₀ a₁ b₀ b₁ c₀ c₁ : α}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hAB : Disjoint ({a₀, a₁} : Set α) ({b₀, b₁} : Set α))
    (hBC : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hAC : Disjoint ({a₀, a₁} : Set α) ({c₀, c₁} : Set α))
    (hA : N.IsBase ({a₀, a₁} : Set α))
    (hB : N.IsBase ({b₀, b₁} : Set α))
    (hC : N.IsBase ({c₀, c₁} : Set α))
    (hABij : BijectionRelation (crossBaseRelation N a₀ a₁ b₀ b₁))
    (hBCij : BijectionRelation (crossBaseRelation N b₀ b₁ c₀ c₁)) :
    ¬ CyclicSatisfiable
      [crossBaseRelation N a₀ a₁ b₀ b₁,
       crossBaseRelation N b₀ b₁ c₀ c₁,
       crossBaseRelation N c₀ c₁ a₀ a₁] := by
  intro hcyc
  simp only [CyclicSatisfiable, composeList, comp, idRel] at hcyc
  rcases hcyc with ⟨x, y, hxy, z, hyz, hzx⟩

  let a := bitPick a₀ a₁ x
  let b' := bitPick b₀ b₁ (Bool.not y)
  let c := bitPick c₀ c₁ z

  have hABnotRel : ¬ crossBaseRelation N a₀ a₁ b₀ b₁ x (Bool.not y) := by
    intro hbad
    have hEq := hABij.2 hxy hbad
    cases y <;> simp at hEq
  have hBCnotRel : ¬ crossBaseRelation N b₀ b₁ c₀ c₁ (Bool.not y) z := by
    intro hbad
    have hEq := cofunctional_of_bijection hBCij hbad hyz
    cases y <;> simp at hEq

  have hab' : a ≠ b' := by
    dsimp [a, b']
    exact bitPick_ne_of_disjoint hAB x (Bool.not y)
  have hb'c : b' ≠ c := by
    dsimp [b', c]
    exact bitPick_ne_of_disjoint hBC (Bool.not y) z
  have hac : a ≠ c := by
    dsimp [a, c]
    exact bitPick_ne_of_disjoint hAC x z

  have hABnotBase : ¬ N.IsBase ({a, b'} : Set α) := by
    simpa [crossBaseRelation, a, b'] using hABnotRel
  have hBCnotBase : ¬ N.IsBase ({b', c} : Set α) := by
    simpa [crossBaseRelation, b', c] using hBCnotRel

  have hABdep : ¬ N.Indep ({a, b'} : Set α) := by
    intro hI
    exact hABnotBase
      (AdjacentRepair.pair_indep_isBase_of_pair_isBase N ha hab' hA hI)
  have hBCdep : ¬ N.Indep ({b', c} : Set α) := by
    intro hI
    exact hBCnotBase
      (AdjacentRepair.pair_indep_isBase_of_pair_isBase N hb hb'c hB hI)

  have haN : N.IsNonloop a := by
    apply hA.indep.isNonloop_of_mem
    simpa [a] using bitPick_mem_pair a₀ a₁ x
  have hbN : N.IsNonloop b' := by
    apply hB.indep.isNonloop_of_mem
    simpa [b'] using bitPick_mem_pair b₀ b₁ (Bool.not y)
  have hcN : N.IsNonloop c := by
    apply hC.indep.isNonloop_of_mem
    simpa [c] using bitPick_mem_pair c₀ c₁ z

  have hclAB : N.closure {a} = N.closure {b'} :=
    (haN.closure_eq_closure_iff_eq_or_dep hbN).2 (Or.inr hABdep)
  have hclBC : N.closure {b'} = N.closure {c} :=
    (hbN.closure_eq_closure_iff_eq_or_dep hcN).2 (Or.inr hBCdep)
  have hclAC : N.closure {a} = N.closure {c} := hclAB.trans hclBC
  rcases (haN.closure_eq_closure_iff_eq_or_dep hcN).1 hclAC with hEq | hACdep
  · exact hac hEq
  · have hCA : N.IsBase ({c, a} : Set α) := by
      simpa [crossBaseRelation, c, a] using hzx
    exact hACdep (by simpa [Set.pair_comm] using hCA.indep)

/-- In the rank-two triangle, two forced sides force the third side to be
forced as well. Otherwise the third relation would provide Boolean slack and
hence a cyclic solution, contradicting the triangle obstruction. -/
theorem crossBaseRelation_triangle_third_bijection
    (N : Matroid α) {a₀ a₁ b₀ b₁ c₀ c₁ : α}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hAB : Disjoint ({a₀, a₁} : Set α) ({b₀, b₁} : Set α))
    (hBC : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hAC : Disjoint ({a₀, a₁} : Set α) ({c₀, c₁} : Set α))
    (hA : N.IsBase ({a₀, a₁} : Set α))
    (hB : N.IsBase ({b₀, b₁} : Set α))
    (hC : N.IsBase ({c₀, c₁} : Set α))
    (hABij : BijectionRelation (crossBaseRelation N a₀ a₁ b₀ b₁))
    (hBCij : BijectionRelation (crossBaseRelation N b₀ b₁ c₀ c₁)) :
    BijectionRelation (crossBaseRelation N c₀ c₁ a₀ a₁) := by
  let RAB := crossBaseRelation N a₀ a₁ b₀ b₁
  let RBC := crossBaseRelation N b₀ b₁ c₀ c₁
  let RCA := crossBaseRelation N c₀ c₁ a₀ a₁
  have hCAfull : FullSupport RCA := by
    dsimp [RCA]
    exact crossBaseRelation_fullSupport N hc ha hAC.symm hC hA
  have hfull : ∀ R ∈ [RAB, RBC, RCA], FullSupport R := by
    intro R hR
    simp only [List.mem_cons, List.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact hABij.1
    · exact hBCij.1
    · exact hCAfull
  by_contra hnot
  have hcyc : CyclicSatisfiable [RAB, RBC, RCA] :=
    cyclicSatisfiable_of_exists_not_bijection hfull ⟨RCA, by simp, hnot⟩
  exact (crossBaseRelation_triangle_not_cyclicSatisfiable
    N ha hb hc hAB hBC hAC hA hB hC hABij hBCij) hcyc

/-- Representation-free triangle parity law. Under the same three-base
hypotheses, two forced sides force the third side to be forced, and the three
identity/flip orientations have odd parity. -/
theorem crossBaseRelation_triangle_odd_parity
    (N : Matroid α) {a₀ a₁ b₀ b₁ c₀ c₁ : α}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hAB : Disjoint ({a₀, a₁} : Set α) ({b₀, b₁} : Set α))
    (hBC : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hAC : Disjoint ({a₀, a₁} : Set α) ({c₀, c₁} : Set α))
    (hA : N.IsBase ({a₀, a₁} : Set α))
    (hB : N.IsBase ({b₀, b₁} : Set α))
    (hC : N.IsBase ({c₀, c₁} : Set α))
    (hABij : BijectionRelation (crossBaseRelation N a₀ a₁ b₀ b₁))
    (hBCij : BijectionRelation (crossBaseRelation N b₀ b₁ c₀ c₁)) :
    (crossBaseRelation N a₀ a₁ b₀ b₁ = idRel ∧
       crossBaseRelation N b₀ b₁ c₀ c₁ = idRel ∧
       crossBaseRelation N c₀ c₁ a₀ a₁ = flipRel) ∨
    (crossBaseRelation N a₀ a₁ b₀ b₁ = idRel ∧
       crossBaseRelation N b₀ b₁ c₀ c₁ = flipRel ∧
       crossBaseRelation N c₀ c₁ a₀ a₁ = idRel) ∨
    (crossBaseRelation N a₀ a₁ b₀ b₁ = flipRel ∧
       crossBaseRelation N b₀ b₁ c₀ c₁ = idRel ∧
       crossBaseRelation N c₀ c₁ a₀ a₁ = idRel) ∨
    (crossBaseRelation N a₀ a₁ b₀ b₁ = flipRel ∧
       crossBaseRelation N b₀ b₁ c₀ c₁ = flipRel ∧
       crossBaseRelation N c₀ c₁ a₀ a₁ = flipRel) := by
  have hCAij := crossBaseRelation_triangle_third_bijection
    N ha hb hc hAB hBC hAC hA hB hC hABij hBCij
  apply (not_cyclicSatisfiable_three_bijections_iff hABij hBCij hCAij).1
  exact crossBaseRelation_triangle_not_cyclicSatisfiable
    N ha hb hc hAB hBC hAC hA hB hC hABij hBCij

end PairCycle
end HigherRankKUM
