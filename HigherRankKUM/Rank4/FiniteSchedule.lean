import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace HigherRankKUM
namespace FiniteSchedule

open Set

noncomputable section

variable {α : Type*}

/-- Enumerate a finite set of size k+1 while prescribing three distinct
entries at positions 0, k-1, and k.

The proof starts from an arbitrary equivalence and uses
Equiv.Perm.exists_extending_pair to move the three desired elements into the
three desired slots simultaneously. -/
theorem exists_fin_equiv_with_three_prescribed
    {S : Set α} {k : ℕ}
    (hk : 2 ≤ k)
    (hS : S.Finite)
    (hcard : S.ncard = k + 1)
    {q p d : α}
    (hq : q ∈ S) (hp : p ∈ S) (hd : d ∈ S)
    (hqp : q ≠ p) (hqd : q ≠ d) (hpd : p ≠ d) :
    ∃ e : Fin (k + 1) ≃ S,
      (e ⟨0, by omega⟩ : α) = q ∧
      (e ⟨k - 1, by omega⟩ : α) = p ∧
      (e ⟨k, by omega⟩ : α) = d := by
  letI : Fintype S := hS.fintype
  have hNatCard : Nat.card S = k + 1 := by
    simpa [Nat.card_coe_set_eq] using hcard
  let e₀ : Fin (k + 1) ≃ S :=
    (Finite.equivFinOfCardEq hNatCard).symm

  let f : Fin 3 → Fin (k + 1) := fun i =>
    Fin.cases ⟨0, by omega⟩
      (fun j => Fin.cases ⟨k - 1, by omega⟩
        (fun _ => ⟨k, by omega⟩) j) i
  let g : Fin 3 → Fin (k + 1) := fun i =>
    Fin.cases (e₀.symm ⟨q, hq⟩)
      (fun j => Fin.cases (e₀.symm ⟨p, hp⟩)
        (fun _ => e₀.symm ⟨d, hd⟩) j) i

  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, Fin.ext_iff] at hij ⊢ <;> omega

  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [g] at hij ⊢
    · exact Subtype.ext (e₀.symm.injective hij)
    · exfalso
      have := congrArg e₀ hij
      simp only [e₀, Equiv.apply_symm_apply] at this
      exact hqp (Subtype.ext_iff.mp this)
    · exfalso
      have := congrArg e₀ hij
      simp only [e₀, Equiv.apply_symm_apply] at this
      exact hqd (Subtype.ext_iff.mp this)
    · exfalso
      have := congrArg e₀ hij
      simp only [e₀, Equiv.apply_symm_apply] at this
      exact hqp (Subtype.ext_iff.mp this).symm
    · exact Subtype.ext (e₀.symm.injective hij)
    · exfalso
      have := congrArg e₀ hij
      simp only [e₀, Equiv.apply_symm_apply] at this
      exact hpd (Subtype.ext_iff.mp this)
    · exfalso
      have := congrArg e₀ hij
      simp only [e₀, Equiv.apply_symm_apply] at this
      exact hqd (Subtype.ext_iff.mp this).symm
    · exfalso
      have := congrArg e₀ hij
      simp only [e₀, Equiv.apply_symm_apply] at this
      exact hpd (Subtype.ext_iff.mp this).symm
    · exact Subtype.ext (e₀.symm.injective hij)

  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  let e : Fin (k + 1) ≃ S := π.trans e₀
  refine ⟨e, ?_, ?_, ?_⟩
  · have h := hπ (0 : Fin 3)
    change (e₀ (π ⟨0, by omega⟩) : α) = q
    simpa [f, g] using congrArg (fun x => (e₀ x : α)) h
  · have h := hπ (1 : Fin 3)
    change (e₀ (π ⟨k - 1, by omega⟩) : α) = p
    simpa [f, g] using congrArg (fun x => (e₀ x : α)) h
  · have h := hπ (2 : Fin 3)
    change (e₀ (π ⟨k, by omega⟩) : α) = d
    simpa [f, g] using congrArg (fun x => (e₀ x : α)) h

end

end FiniteSchedule
end HigherRankKUM
