import Rank3KUM.CyclicOrder
import Mathlib.Tactic

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/-- The `k = 1` rank-three case: the three-element ground set itself is a basis. -/
theorem exists_cyclicBasisOrder3_of_ground_encard_three
    (M : Matroid α)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = (3 : ℕ∞)) :
    ∃ order : Fin 3 ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hEncard : M.E.ncard = 3 := by
    have hcast : (M.E.ncard : ℕ∞) = (3 : ℕ∞) := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast
  let : Fintype M.E := hE.fintype
  have hNatCard : Nat.card M.E = 3 := by
    simpa only [Nat.card_coe_set_eq] using hEncard
  let order : Fin 3 ≃ M.E :=
    (Finite.equivFinOfCardEq hNatCard).symm
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hBcard : B.encard = (3 : ℕ∞) :=
    hB.encard_eq_eRank.trans hRank
  have hBfinite : B.Finite :=
    Set.finite_of_encard_eq_coe hBcard
  have hBE : B = M.E :=
    hBfinite.eq_of_subset_of_encard_le
      hB.subset_ground (by rw [hBcard, hEcard])
  have hGroundBase : M.IsBase M.E := by
    rwa [← hBE]
  have hAll :
      ({(order (0 : Fin 3) : α),
        (order (1 : Fin 3) : α),
        (order (2 : Fin 3) : α)} : Set α) =
        M.E := by
    ext e
    constructor
    · intro he
      simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at he
      rcases he with he | he | he <;> subst e
      · exact (order 0).property
      · exact (order 1).property
      · exact (order 2).property
    · intro he
      obtain ⟨j, hj⟩ :=
        order.surjective (⟨e, he⟩ : M.E)
      have hjcoe : (order j : α) = e :=
        congrArg Subtype.val hj
      fin_cases j
      · exact Set.mem_insert_iff.2 (Or.inl hjcoe.symm)
      · exact Set.mem_insert_iff.2
          (Or.inr (Set.mem_insert_iff.2
            (Or.inl hjcoe.symm)))
      · exact Set.mem_insert_iff.2
          (Or.inr (Set.mem_insert_iff.2
            (Or.inr (Set.mem_singleton_iff.2
              hjcoe.symm))))
  refine ⟨order, ?_⟩
  intro i
  have hwindow :
      ({(order i : α),
        (order (cyclicIndex 3 (by omega) i 1) : α),
        (order (cyclicIndex 3 (by omega) i 2) : α)} :
          Set α) =
        ({(order (0 : Fin 3) : α),
          (order (1 : Fin 3) : α),
          (order (2 : Fin 3) : α)} : Set α) := by
    fin_cases i <;>
      ext x <;>
      simp [cyclicIndex] <;>
      tauto
  rw [hwindow, hAll]
  exact hGroundBase

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_ground_encard_three

end

end Rank3KUM
