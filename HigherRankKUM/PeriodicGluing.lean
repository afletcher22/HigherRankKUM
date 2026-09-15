import HigherRankKUM.PeriodicWindow
import HigherRankKUM.BalancedGluing

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
Density-free periodic restriction/contraction gluing.

Suppose the restriction has `a*p` elements and a cyclic basis order of rank
`a*q`, while the contraction has `b*p` elements and a cyclic basis order of
rank `b*q`. Interleaving them as `(L^a R^b)^p` gives a cyclic basis order of
rank `(a+b)*q` on `(a+b)*p` elements.

No density assumption is used here. The only matroid input is the standard
restriction/contraction basis-union property, delegated to `GenericGluing`.
-/
theorem exists_cyclicBasisOrder_of_periodic_restrict_contract
    (M : Matroid α) {X : Set α} {a b p q : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hX : X ⊆ M.E)
    (σL : Fin (a * p) ≃ (Matroid.restrict M X).E)
    (σR : Fin (b * p) ≃ (Matroid.contract M X).E)
    (hL : CyclicBasisOrder (Matroid.restrict M X) (a * q)
      (Nat.mul_pos ha hp) σL)
    (hR : CyclicBasisOrder (Matroid.contract M X) (b * q)
      (Nat.mul_pos hb hp) σR) :
    ∃ σ : Fin ((a + b) * p) ≃ M.E,
      CyclicBasisOrder M ((a + b) * q)
        (Nat.mul_pos (by omega) hp) σ := by
  let left : Fin (a * p) ≃ X :=
    σL.trans (restrictGroundEquiv M X)
  let right : Fin (b * p) ≃ (M.E \ X : Set α) :=
    σR.trans (contractGroundEquiv M X)
  have hDisjoint : Disjoint X (M.E \ X) :=
    Set.disjoint_sdiff_right
  let localOrder : Fin ((a + b) * p) ≃
      (X ∪ (M.E \ X) : Set α) :=
    balancedBlockOrder hDisjoint left right
  have hUnion : X ∪ (M.E \ X) = M.E :=
    Set.union_sdiff_cancel hX
  let order : Fin ((a + b) * p) ≃ M.E :=
    localOrder.trans (Equiv.setCongr hUnion)
  refine ⟨order, ?_⟩
  have hCore :
      CyclicBasisOrder M (a * q + b * q)
        (Nat.mul_pos (by omega) hp) order := by
    apply cyclicBasisOrder_of_restrict_contract_window_decomposition
      M hX (Nat.mul_pos (by omega) hp)
        (Nat.mul_pos ha hp) (Nat.mul_pos hb hp)
        order σL σR hL hR
    intro z
    obtain ⟨iL, iR, hz⟩ :=
      cyclicWindow_balancedBlockOrder_scaled_decomposition
        (q := q) ha hb hp hDisjoint left right z
    refine ⟨iL, iR, ?_⟩
    simpa only [order, localOrder, left, right,
      cyclicWindow, Equiv.trans_apply, Equiv.setCongr_apply,
      restrictGroundEquiv_apply_coe,
      contractGroundEquiv_apply_coe,
      Nat.add_mul] using hz
  simpa [Nat.add_mul] using hCore

end

end HigherRankKUM
