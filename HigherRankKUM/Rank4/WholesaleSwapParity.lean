import HigherRankKUM.Rank4.ThreePairTriangle
import HigherRankKUM.BinaryRelationTriangleParity

namespace HigherRankKUM
namespace Rank4ThreePairDual

open Set
open BinaryRelationCycle

variable {α : Type*}

/-- Representation-free parity conservation for the wholesale swap of the
middle two pair blocks in a six-block rank-four configuration.

Write

`R₁ = T(A,B,C)`, `R₂ = T(B,C,D)`, `R₃ = T(C,D,E)`, `R₄ = T(D,E,F)`

for the four old affected middle-pair relations and

`S₁ = T(A,B,D)`, `S₂ = T(B,D,C)`, `S₃ = T(D,C,E)`, `S₄ = T(C,E,F)`

for the four relations after swapping `C,D`.  The auxiliary relations are

`U = T(C,B,D)` and `V = T(C,E,D)`.

If all ten relations are forced Boolean bijections, then the old four-cycle
is cyclically satisfiable exactly when the new four-cycle is.  Equivalently,
the total identity/flip parity of the four affected forced relations is
preserved.

The proof is intrinsic.  Two contraction triangles and two six-element dual
triangles are odd; the auxiliary bits `U,V` cancel pairwise.  No field,
representation, simplicity, or global rank hypothesis is used beyond the
listed local basis data. -/
theorem wholesaleSwap_middlePairRelations_preserve_cyclicSatisfiable
    (M : Matroid α)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ e₀ e₁ f₀ f₁ : α}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hd : d₀ ≠ d₁) (he : e₀ ≠ e₁) (hf : f₀ ≠ f₁)
    (hAB : Disjoint ({a₀, a₁} : Set α) ({b₀, b₁} : Set α))
    (hAC : Disjoint ({a₀, a₁} : Set α) ({c₀, c₁} : Set α))
    (hAD : Disjoint ({a₀, a₁} : Set α) ({d₀, d₁} : Set α))
    (hBC : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hBD : Disjoint ({b₀, b₁} : Set α) ({d₀, d₁} : Set α))
    (hCD : Disjoint ({c₀, c₁} : Set α) ({d₀, d₁} : Set α))
    (hCE : Disjoint ({c₀, c₁} : Set α) ({e₀, e₁} : Set α))
    (hCF : Disjoint ({c₀, c₁} : Set α) ({f₀, f₁} : Set α))
    (hDE : Disjoint ({d₀, d₁} : Set α) ({e₀, e₁} : Set α))
    (hDF : Disjoint ({d₀, d₁} : Set α) ({f₀, f₁} : Set α))
    (hEF : Disjoint ({e₀, e₁} : Set α) ({f₀, f₁} : Set α))
    (hABbase : M.IsBase (({a₀, a₁} : Set α) ∪ {b₀, b₁}))
    (hBCbase : M.IsBase (({b₀, b₁} : Set α) ∪ {c₀, c₁}))
    (hBDbase : M.IsBase (({b₀, b₁} : Set α) ∪ {d₀, d₁}))
    (hCDbase : M.IsBase (({c₀, c₁} : Set α) ∪ {d₀, d₁}))
    (hCEbase : M.IsBase (({c₀, c₁} : Set α) ∪ {e₀, e₁}))
    (hDEbase : M.IsBase (({d₀, d₁} : Set α) ∪ {e₀, e₁}))
    (hEFbase : M.IsBase (({e₀, e₁} : Set α) ∪ {f₀, f₁}))
    (hR₁ : BijectionRelation (middlePairRelation M a₀ a₁ b₀ b₁ c₀ c₁))
    (hR₂ : BijectionRelation (middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁))
    (hR₃ : BijectionRelation (middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁))
    (hR₄ : BijectionRelation (middlePairRelation M d₀ d₁ e₀ e₁ f₀ f₁))
    (hS₁ : BijectionRelation (middlePairRelation M a₀ a₁ b₀ b₁ d₀ d₁))
    (hS₂ : BijectionRelation (middlePairRelation M b₀ b₁ d₀ d₁ c₀ c₁))
    (hS₃ : BijectionRelation (middlePairRelation M d₀ d₁ c₀ c₁ e₀ e₁))
    (hS₄ : BijectionRelation (middlePairRelation M c₀ c₁ e₀ e₁ f₀ f₁))
    (hU : BijectionRelation (middlePairRelation M c₀ c₁ b₀ b₁ d₀ d₁))
    (hV : BijectionRelation (middlePairRelation M c₀ c₁ e₀ e₁ d₀ d₁)) :
    CyclicSatisfiable
      [middlePairRelation M a₀ a₁ b₀ b₁ c₀ c₁,
       middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁,
       middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁,
       middlePairRelation M d₀ d₁ e₀ e₁ f₀ f₁] ↔
    CyclicSatisfiable
      [middlePairRelation M a₀ a₁ b₀ b₁ d₀ d₁,
       middlePairRelation M b₀ b₁ d₀ d₁ c₀ c₁,
       middlePairRelation M d₀ d₁ c₀ c₁ e₀ e₁,
       middlePairRelation M c₀ c₁ e₀ e₁ f₀ f₁] := by
  have hrevS₁ :
      middlePairRelation M d₀ d₁ b₀ b₁ a₀ a₁ =
        middlePairRelation M a₀ a₁ b₀ b₁ d₀ d₁ := by
    calc
      middlePairRelation M d₀ d₁ b₀ b₁ a₀ a₁ =
          transpose (middlePairRelation M a₀ a₁ b₀ b₁ d₀ d₁) :=
        middlePairRelation_reverse M a₀ a₁ b₀ b₁ d₀ d₁
      _ = middlePairRelation M a₀ a₁ b₀ b₁ d₀ d₁ :=
        transpose_eq_self_of_bijection hS₁
  have hL₁ := middlePairRelation_contract_triangle_not_cyclicSatisfiable M
    ha hc hd hAB hBC.symm hBD.symm hAC hCD hAD
    hABbase
    (by simpa [Set.union_comm] using hBCbase)
    (by simpa [Set.union_comm] using hBDbase)
    hR₁ hU
  rw [hrevS₁] at hL₁

  have hrevR₂ :
      middlePairRelation M d₀ d₁ c₀ c₁ b₀ b₁ =
        middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁ := by
    calc
      middlePairRelation M d₀ d₁ c₀ c₁ b₀ b₁ =
          transpose (middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁) :=
        middlePairRelation_reverse M b₀ b₁ c₀ c₁ d₀ d₁
      _ = middlePairRelation M b₀ b₁ c₀ c₁ d₀ d₁ :=
        transpose_eq_self_of_bijection hR₂
  have hL₂ := middlePairRelation_triangle_not_cyclicSatisfiable M
    hb hd hc hBD hCD.symm hBC
    hBDbase
    (by simpa [Set.union_comm] using hCDbase)
    hBCbase
    hS₂ hU
  rw [hrevR₂] at hL₂

  have hrevR₃ :
      middlePairRelation M e₀ e₁ d₀ d₁ c₀ c₁ =
        middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁ := by
    calc
      middlePairRelation M e₀ e₁ d₀ d₁ c₀ c₁ =
          transpose (middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁) :=
        middlePairRelation_reverse M c₀ c₁ d₀ d₁ e₀ e₁
      _ = middlePairRelation M c₀ c₁ d₀ d₁ e₀ e₁ :=
        transpose_eq_self_of_bijection hR₃
  have hRight₁ := middlePairRelation_triangle_not_cyclicSatisfiable M
    hc he hd hCE hDE.symm hCD
    hCEbase
    (by simpa [Set.union_comm] using hDEbase)
    hCDbase
    hV hS₃
  rw [hrevR₃] at hRight₁

  have hrevS₄ :
      middlePairRelation M f₀ f₁ e₀ e₁ c₀ c₁ =
        middlePairRelation M c₀ c₁ e₀ e₁ f₀ f₁ := by
    calc
      middlePairRelation M f₀ f₁ e₀ e₁ c₀ c₁ =
          transpose (middlePairRelation M c₀ c₁ e₀ e₁ f₀ f₁) :=
        middlePairRelation_reverse M c₀ c₁ e₀ e₁ f₀ f₁
      _ = middlePairRelation M c₀ c₁ e₀ e₁ f₀ f₁ :=
        transpose_eq_self_of_bijection hS₄
  have hRight₂ := middlePairRelation_contract_triangle_not_cyclicSatisfiable M
    hc hd hf hCE hDE hEF.symm hCD hDF hCF
    hCEbase hDEbase
    (by simpa [Set.union_comm] using hEFbase)
    hV hR₄
  rw [hrevS₄] at hRight₂

  exact cyclicSatisfiable_four_iff_of_shared_triangle_obstructions
    hR₁ hR₂ hR₃ hR₄ hS₁ hS₂ hS₃ hS₄ hU hV
    hL₁ hL₂ hRight₁ hRight₂

end Rank4ThreePairDual
end HigherRankKUM
