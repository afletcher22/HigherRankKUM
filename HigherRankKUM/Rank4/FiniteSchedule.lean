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


/-- Slot type for the t=3 schedule: A-slots, B-slots, C-slots, and G-slots. -/
abbrev T3Slots (k : ℕ) :=
  (Fin (k + 1) ⊕ Fin (k + 1)) ⊕ (Fin (k + 1) ⊕ Fin (k - 1))

private def t3PrefixSlot {k : ℕ} (j : Fin (k - 1)) : Fin 4 → T3Slots k :=
  Fin.cases (Sum.inl (Sum.inl ⟨j.val, by omega⟩))
    (fun r =>
      Fin.cases (Sum.inl (Sum.inr ⟨j.val, by omega⟩))
        (fun s =>
          Fin.cases (Sum.inr (Sum.inl ⟨j.val, by omega⟩))
            (fun _ => Sum.inr (Sum.inr j)) s) r)

private def t3TailSlot {k : ℕ} (hk : 2 ≤ k) : Fin 6 → T3Slots k :=
  Fin.cases (Sum.inl (Sum.inl ⟨k - 1, by omega⟩))
    (fun r =>
      Fin.cases (Sum.inl (Sum.inr ⟨k - 1, by omega⟩))
        (fun s =>
          Fin.cases (Sum.inr (Sum.inl ⟨k - 1, by omega⟩))
            (fun t =>
              Fin.cases (Sum.inl (Sum.inl ⟨k, by omega⟩))
                (fun u =>
                  Fin.cases (Sum.inl (Sum.inr ⟨k, by omega⟩))
                    (fun _ => Sum.inr (Sum.inl ⟨k, by omega⟩)) u) t) s) r)

/-- Regroup the explicit t=3 block-plus-tail positions into the four local
slot families A,B,C,G. -/
def t3RegroupEquiv (k : ℕ) (hk : 2 ≤ k) :
    (Fin (k - 1) × Fin 4) ⊕ Fin 6 ≃ T3Slots k := by
  let f : (Fin (k - 1) × Fin 4) ⊕ Fin 6 → T3Slots k
    | Sum.inl x => t3PrefixSlot x.1 x.2
    | Sum.inr r => t3TailSlot hk r
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · rcases x with ⟨i, r⟩
      rcases y with ⟨j, s⟩
      fin_cases r <;> fin_cases s <;>
        simp [f, t3PrefixSlot, Fin.ext_iff] at hxy ⊢ <;> omega
    · rcases x with ⟨i, r⟩
      fin_cases r <;> fin_cases y <;>
        simp [f, t3PrefixSlot, t3TailSlot, Fin.ext_iff] at hxy
    · rcases y with ⟨j, s⟩
      fin_cases x <;> fin_cases s <;>
        simp [f, t3PrefixSlot, t3TailSlot, Fin.ext_iff] at hxy
    · fin_cases x <;> fin_cases y <;>
        simp [f, t3TailSlot, Fin.ext_iff] at hxy ⊢ <;> omega
  · intro y
    rcases y with (a | b) | (c | g)
    · by_cases hlt : a.val < k - 1
      · refine ⟨Sum.inl (⟨a.val, hlt⟩, 0), ?_⟩
        simp [f, t3PrefixSlot, Fin.ext_iff]
      · have ha : a.val = k - 1 ∨ a.val = k := by omega
        rcases ha with ha | ha
        · refine ⟨Sum.inr 0, ?_⟩
          subst a
          simp [f, t3TailSlot, Fin.ext_iff]
        · refine ⟨Sum.inr 3, ?_⟩
          subst a
          simp [f, t3TailSlot, Fin.ext_iff]
    · by_cases hlt : b.val < k - 1
      · refine ⟨Sum.inl (⟨b.val, hlt⟩, 1), ?_⟩
        simp [f, t3PrefixSlot, Fin.ext_iff]
      · have hb : b.val = k - 1 ∨ b.val = k := by omega
        rcases hb with hb | hb
        · refine ⟨Sum.inr 1, ?_⟩
          subst b
          simp [f, t3TailSlot, Fin.ext_iff]
        · refine ⟨Sum.inr 4, ?_⟩
          subst b
          simp [f, t3TailSlot, Fin.ext_iff]
    · by_cases hlt : c.val < k - 1
      · refine ⟨Sum.inl (⟨c.val, hlt⟩, 2), ?_⟩
        simp [f, t3PrefixSlot, Fin.ext_iff]
      · have hc : c.val = k - 1 ∨ c.val = k := by omega
        rcases hc with hc | hc
        · refine ⟨Sum.inr 2, ?_⟩
          subst c
          simp [f, t3TailSlot, Fin.ext_iff]
        · refine ⟨Sum.inr 5, ?_⟩
          subst c
          simp [f, t3TailSlot, Fin.ext_iff]
    · refine ⟨Sum.inl (g, 3), ?_⟩
      simp [f, t3PrefixSlot, Fin.ext_iff]

/-- The canonical index decomposition of the t=3 schedule into ordinary
ABCG blocks followed by six tail positions. -/
def t3BlockTailEquiv (k : ℕ) (hk : 2 ≤ k) :
    Fin (4 * k + 2) ≃ (Fin (k - 1) × Fin 4) ⊕ Fin 6 := by
  have hcard : (k - 1) * 4 + 6 = 4 * k + 2 := by omega
  exact (finCongr hcard.symm).trans
    ((finSumFinEquiv :
      Fin ((k - 1) * 4) ⊕ Fin 6 ≃ Fin ((k - 1) * 4 + 6)).symm.trans
      (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _)))

/-- Canonical pure-index equivalence from global t=3 positions to the four
local slot families. -/
def t3IndexEquiv (k : ℕ) (hk : 2 ≤ k) :
    Fin (4 * k + 2) ≃ T3Slots k :=
  (t3BlockTailEquiv k hk).trans (t3RegroupEquiv k hk)

end

end FiniteSchedule
end HigherRankKUM
