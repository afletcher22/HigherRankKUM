import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace HigherRankKUM
namespace FiniteSchedule

open Set

noncomputable section

variable {α : Type*}

/-- Enumerate a finite set of size k+1 while prescribing three distinct
entries at positions 0, k-1, and k. -/
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
  let pos : Fin 3 → Fin (k + 1) :=
    ![⟨0, by omega⟩, ⟨k - 1, by omega⟩, ⟨k, by omega⟩]
  let val : Fin 3 → S :=
    ![⟨q, hq⟩, ⟨p, hp⟩, ⟨d, hd⟩]
  have hpos : Function.Injective pos := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [pos, Fin.ext_iff] at hij ⊢ <;> omega
  have hval : Function.Injective val := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [val, hqp, hqd, hpd] at hij ⊢
  let target : Fin 3 → Fin (k + 1) := fun i => e₀.symm (val i)
  have htarget : Function.Injective target :=
    e₀.symm.injective.comp hval
  obtain ⟨π, hπ⟩ :=
    Equiv.Perm.exists_extending_pair pos target hpos htarget
  let e : Fin (k + 1) ≃ S := π.trans e₀
  refine ⟨e, ?_, ?_, ?_⟩
  · have h0 :
        π ⟨0, by omega⟩ = e₀.symm ⟨q, hq⟩ := by
      simpa [pos, target, val] using hπ (0 : Fin 3)
    change (e₀ (π ⟨0, by omega⟩) : α) = q
    rw [h0]
    simp
  · have h1 :
        π ⟨k - 1, by omega⟩ = e₀.symm ⟨p, hp⟩ := by
      simpa [pos, target, val] using hπ (1 : Fin 3)
    change (e₀ (π ⟨k - 1, by omega⟩) : α) = p
    rw [h1]
    simp
  · have h2 :
        π ⟨k, by omega⟩ = e₀.symm ⟨d, hd⟩ := by
      simpa [pos, target, val] using hπ (2 : Fin 3)
    change (e₀ (π ⟨k, by omega⟩) : α) = d
    rw [h2]
    simp

/-- Slot type for the t=3 schedule: A-slots, B-slots, C-slots, and G-slots. -/
abbrev T3Slots (k : ℕ) :=
  (Fin (k + 1) ⊕ Fin (k + 1)) ⊕ (Fin (k + 1) ⊕ Fin (k - 1))

def t3PrefixSlot {k : ℕ} (j : Fin (k - 1)) : Fin 4 → T3Slots k :=
  ![Sum.inl (Sum.inl ⟨j.val, by omega⟩),
    Sum.inl (Sum.inr ⟨j.val, by omega⟩),
    Sum.inr (Sum.inl ⟨j.val, by omega⟩),
    Sum.inr (Sum.inr j)]

def t3TailSlot {k : ℕ} (hk : 2 ≤ k) : Fin 6 → T3Slots k :=
  ![Sum.inl (Sum.inl ⟨k - 1, by omega⟩),
    Sum.inl (Sum.inr ⟨k - 1, by omega⟩),
    Sum.inr (Sum.inl ⟨k - 1, by omega⟩),
    Sum.inl (Sum.inl ⟨k, by omega⟩),
    Sum.inl (Sum.inr ⟨k, by omega⟩),
    Sum.inr (Sum.inl ⟨k, by omega⟩)]

/-- Regroup the explicit t=3 block-plus-tail positions into the four local
slot families A,B,C,G. -/
def t3RegroupEquiv (k : ℕ) (hk : 2 ≤ k) :
    (Fin (k - 1) × Fin 4) ⊕ Fin 6 ≃ T3Slots k := by
  let f : (Fin (k - 1) × Fin 4) ⊕ Fin 6 → T3Slots k
    | Sum.inl x => t3PrefixSlot x.1 x.2
    | Sum.inr r => t3TailSlot hk r
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_surjective_and_card f).2
  refine ⟨?_, ?_⟩
  · intro y
    rcases y with (a | b) | (cc | g)
    · by_cases ha : a.val < k - 1
      · refine ⟨Sum.inl (⟨a.val, ha⟩, 0), ?_⟩
        simp [f, t3PrefixSlot, Fin.ext_iff]
      · have haCases : a.val = k - 1 ∨ a.val = k := by
          omega
        rcases haCases with haEq | haEq
        · refine ⟨Sum.inr 0, ?_⟩
          simp [f, t3TailSlot, Fin.ext_iff, haEq]
        · refine ⟨Sum.inr 3, ?_⟩
          simp [f, t3TailSlot, Fin.ext_iff, haEq]
    · by_cases hb : b.val < k - 1
      · refine ⟨Sum.inl (⟨b.val, hb⟩, 1), ?_⟩
        simp [f, t3PrefixSlot, Fin.ext_iff]
      · have hbCases : b.val = k - 1 ∨ b.val = k := by
          omega
        rcases hbCases with hbEq | hbEq
        · refine ⟨Sum.inr 1, ?_⟩
          simp [f, t3TailSlot, Fin.ext_iff, hbEq]
        · refine ⟨Sum.inr 4, ?_⟩
          simp [f, t3TailSlot, Fin.ext_iff, hbEq]
    · by_cases hc : cc.val < k - 1
      · refine ⟨Sum.inl (⟨cc.val, hc⟩, 2), ?_⟩
        simp [f, t3PrefixSlot, Fin.ext_iff]
      · have hcCases : cc.val = k - 1 ∨ cc.val = k := by
          omega
        rcases hcCases with hcEq | hcEq
        · refine ⟨Sum.inr 2, ?_⟩
          simp [f, t3TailSlot, Fin.ext_iff, hcEq]
        · refine ⟨Sum.inr 5, ?_⟩
          simp [f, t3TailSlot, Fin.ext_iff, hcEq]
    · refine ⟨Sum.inl (g, 3), ?_⟩
      simp [f, t3PrefixSlot]
  · simp [T3Slots]
    omega

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


@[simp] theorem t3BlockTailEquiv_symm_prefix
    (k : ℕ) (hk : 2 ≤ k) (j : Fin (k - 1)) (r : Fin 4) :
    (t3BlockTailEquiv k hk).symm (Sum.inl (j, r)) =
      ⟨r.val + 4 * j.val, by omega⟩ := by
  apply Fin.ext
  simp [t3BlockTailEquiv, finProdFinEquiv]
  omega

@[simp] theorem t3BlockTailEquiv_symm_tail
    (k : ℕ) (hk : 2 ≤ k) (r : Fin 6) :
    (t3BlockTailEquiv k hk).symm (Sum.inr r) =
      ⟨4 * (k - 1) + r.val, by omega⟩ := by
  apply Fin.ext
  simp [t3BlockTailEquiv]
  omega

@[simp] theorem t3IndexEquiv_prefix
    (k : ℕ) (hk : 2 ≤ k) (j : Fin (k - 1)) (r : Fin 4) :
    t3IndexEquiv k hk ⟨r.val + 4 * j.val, by omega⟩ =
      t3PrefixSlot j r := by
  have hbt :
      t3BlockTailEquiv k hk ⟨r.val + 4 * j.val, by omega⟩ =
        Sum.inl (j, r) := by
    apply (t3BlockTailEquiv k hk).symm.injective
    simp
  simp [t3IndexEquiv, hbt, t3RegroupEquiv]

@[simp] theorem t3IndexEquiv_tail
    (k : ℕ) (hk : 2 ≤ k) (r : Fin 6) :
    t3IndexEquiv k hk ⟨4 * (k - 1) + r.val, by omega⟩ =
      t3TailSlot hk r := by
  have hbt :
      t3BlockTailEquiv k hk ⟨4 * (k - 1) + r.val, by omega⟩ =
        Sum.inr r := by
    apply (t3BlockTailEquiv k hk).symm.injective
    simp
  simp [t3IndexEquiv, hbt, t3RegroupEquiv]




end

end FiniteSchedule
end HigherRankKUM
