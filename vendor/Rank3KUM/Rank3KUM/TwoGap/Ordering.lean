import Rank3KUM.TwoGap
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/--
A three-element set can be ordered with any two distinct prescribed elements
in the first and final positions.
-/
theorem exists_fin3_equiv_with_endpoints
    {D : Set α} {u w : α}
    (hcard : D.encard = 3)
    (huD : u ∈ D) (hwD : w ∈ D)
    (huw : u ≠ w) :
    ∃ d : Fin 3 ≃ D,
      (d 0 : α) = u ∧ (d 2 : α) = w := by
  classical
  have hDfinite : D.Finite :=
    Set.finite_of_encard_eq_coe hcard
  let : Fintype D := hDfinite.fintype
  have hcardF : Fintype.card D = 3 := by
    have hcardE : (Fintype.card D : ℕ∞) = (3 : ℕ∞) := by
      calc
        (Fintype.card D : ℕ∞) = D.encard := Set.coe_fintypeCard D
        _ = 3 := hcard
    exact_mod_cast hcardE
  let base : Fin 3 ≃ D :=
    (Fintype.equivFinOfCardEq hcardF).symm
  let U : D := ⟨u, huD⟩
  let W : D := ⟨w, hwD⟩
  let first : Fin 3 ≃ D :=
    base.trans (Equiv.swap (base 0) U)
  have hfirst_zero : first 0 = U := by
    simp [first]
  have hfirst_two_ne_U : first 2 ≠ U := by
    intro h
    rw [← hfirst_zero] at h
    exact (by decide : (2 : Fin 3) ≠ 0) (first.injective h)
  have hWU : W ≠ U := by
    intro h
    apply huw
    exact (congrArg Subtype.val h).symm
  let result : Fin 3 ≃ D :=
    first.trans (Equiv.swap (first 2) W)
  refine ⟨result, ?_, ?_⟩
  · have hresult_zero : result 0 = U := by
      change (Equiv.swap (first 2) W) (first 0) = U
      rw [hfirst_zero]
      exact Equiv.swap_apply_of_ne_of_ne
        hfirst_two_ne_U.symm hWU.symm
    exact congrArg Subtype.val hresult_zero
  · have hresult_two : result 2 = W := by
      simp [result]
    exact congrArg Subtype.val hresult_two

/-- The range of an ordering `Fin 3 ≃ D` is exactly its three displayed values. -/
theorem set_eq_triple_of_fin3_equiv
    {D : Set α} (d : Fin 3 ≃ D) :
    D = ({(d 0 : α), (d 1 : α), (d 2 : α)} : Set α) := by
  ext x
  constructor
  · intro hx
    let xD : D := ⟨x, hx⟩
    obtain ⟨i, hi⟩ := d.surjective xD
    have hval : (d i : α) = x :=
      congrArg Subtype.val hi
    fin_cases i <;> simp_all
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · subst x
      exact (d 0).property
    · subst x
      exact (d 1).property
    · subst x
      exact (d 2).property

/-- Distinct positions in a `Fin 3` ordering have distinct underlying values. -/
theorem fin3_equiv_coe_ne
    {D : Set α} (d : Fin 3 ≃ D) {i j : Fin 3}
    (hij : i ≠ j) :
    (d i : α) ≠ (d j : α) := by
  intro h
  apply hij
  apply d.injective
  apply Subtype.ext
  exact h

end Rank3KUM.TwoGap
