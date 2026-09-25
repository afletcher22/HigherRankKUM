import HigherRankKUM.BalancedWindowDecomposition
import Mathlib.Combinatorics.Matroid.Minor.Contract

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/-- Restriction ground elements are value-identical to elements of `X`. -/
def restrictGroundEquiv (M : Matroid α) (X : Set α) :
    (Matroid.restrict M X).E ≃ X where
  toFun e := ⟨e, by simpa using e.property⟩
  invFun e := ⟨e, by simp⟩
  left_inv e := by ext; rfl
  right_inv e := by ext; rfl

/-- Contraction ground elements are value-identical to elements of `M.E \ X`. -/
def contractGroundEquiv (M : Matroid α) (X : Set α) :
    (Matroid.contract M X).E ≃ (M.E \ X : Set α) where
  toFun e := ⟨e, by simpa using e.property⟩
  invFun e := ⟨e, by simp⟩
  left_inv e := by ext; rfl
  right_inv e := by ext; rfl

@[simp] theorem restrictGroundEquiv_apply_coe
    (M : Matroid α) (X : Set α)
    (x : (Matroid.restrict M X).E) :
    (((restrictGroundEquiv M X) x : X) : α) = (x : α) := by
  rfl

@[simp] theorem contractGroundEquiv_apply_coe
    (M : Matroid α) (X : Set α)
    (x : (Matroid.contract M X).E) :
    (((contractGroundEquiv M X) x : (M.E \ X : Set α)) : α) =
      (x : α) := by
  rfl

@[simp] theorem restrictGroundEquiv_trans_apply_coe
    {β : Type*} (M : Matroid α) (X : Set α)
    (σ : β ≃ (Matroid.restrict M X).E) (x : β) :
    (((σ.trans (restrictGroundEquiv M X)) x : X) : α) =
      ((σ x : (Matroid.restrict M X).E) : α) := by
  rfl

@[simp] theorem contractGroundEquiv_trans_apply_coe
    {β : Type*} (M : Matroid α) (X : Set α)
    (σ : β ≃ (Matroid.contract M X).E) (x : β) :
    (((σ.trans (contractGroundEquiv M X)) x :
      (M.E \ X : Set α)) : α) =
      ((σ x : (Matroid.contract M X).E) : α) := by
  rfl

/--
Concrete balanced restriction/contraction gluing in arbitrary rank.

If `M | X` has a cyclic basis order of block size `s` on `s*k` elements and
`M / X` has one of block size `t` on `t*k` elements, then interleaving them
as `(X^s (E\\X)^t)^k` gives a cyclic basis order of `M` of block size `s+t`.
No density or ambient-rank assumption is used by the gluing step itself.
-/
theorem exists_cyclicBasisOrder_of_balanced_restrict_contract
    (M : Matroid α) {X : Set α} {s t k : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hk : 0 < k)
    (hX : X ⊆ M.E)
    (σS : Fin (s * k) ≃ (Matroid.restrict M X).E)
    (σT : Fin (t * k) ≃ (Matroid.contract M X).E)
    (hS : CyclicBasisOrder (Matroid.restrict M X) s
      (Nat.mul_pos hs hk) σS)
    (hT : CyclicBasisOrder (Matroid.contract M X) t
      (Nat.mul_pos ht hk) σT) :
    ∃ σ : Fin ((s + t) * k) ≃ M.E,
      CyclicBasisOrder M (s + t) (Nat.mul_pos (by omega) hk) σ := by
  let left : Fin (s * k) ≃ X :=
    σS.trans (restrictGroundEquiv M X)
  let right : Fin (t * k) ≃ (M.E \ X : Set α) :=
    σT.trans (contractGroundEquiv M X)
  have hDisjoint : Disjoint X (M.E \ X) :=
    Set.disjoint_sdiff_right
  let localOrder : Fin ((s + t) * k) ≃
      (X ∪ (M.E \ X) : Set α) :=
    balancedBlockOrder hDisjoint left right
  have hUnion : X ∪ (M.E \ X) = M.E :=
    Set.union_sdiff_cancel hX
  let order : Fin ((s + t) * k) ≃ M.E :=
    localOrder.trans (Set.equivOfEq hUnion)
  refine ⟨order, ?_⟩
  apply cyclicBasisOrder_of_restrict_contract_window_decomposition
    M hX (Nat.mul_pos (by omega) hk)
      (Nat.mul_pos hs hk) (Nat.mul_pos ht hk)
      order σS σT hS hT
  intro p
  obtain ⟨iS, iT, hp⟩ :=
    cyclicWindow_balancedBlockOrder_decomposition
      hs ht hk hDisjoint left right p
  refine ⟨iS, iT, ?_⟩
  simpa only [order, localOrder, left, right,
    cyclicWindow, Equiv.trans_apply, Set.equivOfEq_apply,
    restrictGroundEquiv_apply_coe,
    contractGroundEquiv_apply_coe] using hp

end

end HigherRankKUM
