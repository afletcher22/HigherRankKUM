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
  let f : Fin 3 → S := fun i =>
    Fin.cases (e₀ ⟨0, by omega⟩)
      (fun j => Fin.cases (e₀ ⟨k - 1, by omega⟩)
        (fun _ => e₀ ⟨k, by omega⟩) j) i
  let g : Fin 3 → S := fun i =>
    Fin.cases ⟨q, hq⟩
      (fun j => Fin.cases ⟨p, hp⟩ (fun _ => ⟨d, hd⟩) j) i
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, Fin.ext_iff] at hij ⊢ <;> omega
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [g, hqp, hqd, hpd] at hij ⊢
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  let e : Fin (k + 1) ≃ S := e₀.trans ρ
  refine ⟨e, ?_, ?_, ?_⟩
  · have h := hρ (0 : Fin 3)
    change (ρ (e₀ ⟨0, by omega⟩) : α) = q
    simpa [f, g] using congrArg Subtype.val h
  · have h := hρ (1 : Fin 3)
    change (ρ (e₀ ⟨k - 1, by omega⟩) : α) = p
    simpa [f, g] using congrArg Subtype.val h
  · have h := hρ (2 : Fin 3)
    change (ρ (e₀ ⟨k, by omega⟩) : α) = d
    simpa [f, g] using congrArg Subtype.val h


/-- Slot type for the t=3 schedule: A-slots, B-slots, C-slots, and G-slots. -/
abbrev T3Slots (k : ℕ) :=
  (Fin (k + 1) ⊕ Fin (k + 1)) ⊕ (Fin (k + 1) ⊕ Fin (k - 1))

def t3PrefixSlot {k : ℕ} (j : Fin (k - 1)) : Fin 4 → T3Slots k :=
  Fin.cases (Sum.inl (Sum.inl ⟨j.val, by omega⟩))
    (fun r =>
      Fin.cases (Sum.inl (Sum.inr ⟨j.val, by omega⟩))
        (fun s =>
          Fin.cases (Sum.inr (Sum.inl ⟨j.val, by omega⟩))
            (fun _ => Sum.inr (Sum.inr j)) s) r)

def t3TailSlot {k : ℕ} (hk : 2 ≤ k) : Fin 6 → T3Slots k :=
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
  apply (Fintype.bijective_iff_injective_and_card f).2
  refine ⟨?_, ?_⟩
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



/-- Enumerate a finite set while prescribing two distinct slots. -/
theorem exists_fin_equiv_with_two_prescribed
    {S : Set α} {n : ℕ}
    (hS : S.Finite) (hcard : S.ncard = n)
    (i j : Fin n) (hij : i ≠ j)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ e : Fin n ≃ S, (e i : α) = x ∧ (e j : α) = y := by
  letI : Fintype S := hS.fintype
  have hNatCard : Nat.card S = n := by
    simpa [Nat.card_coe_set_eq] using hcard
  let e₀ : Fin n ≃ S := (Finite.equivFinOfCardEq hNatCard).symm
  let f : Fin 2 → Fin n := fun r => Fin.cases i (fun _ => j) r
  let g : Fin 2 → Fin n := fun r =>
    Fin.cases (e₀.symm ⟨x, hx⟩) (fun _ => e₀.symm ⟨y, hy⟩) r
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
    · exact (hij hab).elim
    · exact (hij hab.symm).elim
  have hg : Function.Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [g] at hab ⊢
    · have h := congrArg e₀ hab
      simp only [Equiv.apply_symm_apply] at h
      exact (hxy (Subtype.ext_iff.mp h)).elim
    · have h := congrArg e₀ hab
      simp only [Equiv.apply_symm_apply] at h
      exact (hxy (Subtype.ext_iff.mp h).symm).elim
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  let e : Fin n ≃ S := π.trans e₀
  refine ⟨e, ?_, ?_⟩
  · have h := hπ (0 : Fin 2)
    change (e₀ (π i) : α) = x
    simpa [f, g] using congrArg (fun z => (e₀ z : α)) h
  · have h := hπ (1 : Fin 2)
    change (e₀ (π j) : α) = y
    simpa [f, g] using congrArg (fun z => (e₀ z : α)) h

/-- Slot type for the t=2 schedule: A-slots, B-slots, and the 2k core slots. -/
abbrev T2Slots (k : ℕ) :=
  (Fin (k + 1) ⊕ Fin (k + 1)) ⊕ Fin (2 * k)

def t2PrefixSlot {k : ℕ} (j : Fin (k - 1)) : Fin 4 → T2Slots k :=
  Fin.cases (Sum.inl (Sum.inl ⟨j.val, by omega⟩))
    (fun r =>
      Fin.cases (Sum.inl (Sum.inr ⟨j.val, by omega⟩))
        (fun s =>
          Fin.cases (Sum.inr ⟨2 * j.val, by omega⟩)
            (fun _ => Sum.inr ⟨2 * j.val + 1, by omega⟩) s) r)

def t2TailSlot {k : ℕ} (hk : 2 ≤ k) : Fin 6 → T2Slots k :=
  Fin.cases (Sum.inl (Sum.inl ⟨k - 1, by omega⟩))
    (fun r =>
      Fin.cases (Sum.inl (Sum.inr ⟨k - 1, by omega⟩))
        (fun s =>
          Fin.cases (Sum.inr ⟨2 * k - 2, by omega⟩)
            (fun t =>
              Fin.cases (Sum.inl (Sum.inr ⟨k, by omega⟩))
                (fun u =>
                  Fin.cases (Sum.inl (Sum.inl ⟨k, by omega⟩))
                    (fun _ => Sum.inr ⟨2 * k - 1, by omega⟩) u) t) s) r)

/-- Regroup the t=2 block-plus-tail positions into A,B,G local slots. -/
def t2RegroupEquiv (k : ℕ) (hk : 2 ≤ k) :
    (Fin (k - 1) × Fin 4) ⊕ Fin 6 ≃ T2Slots k := by
  let f : (Fin (k - 1) × Fin 4) ⊕ Fin 6 → T2Slots k
    | Sum.inl x => t2PrefixSlot x.1 x.2
    | Sum.inr r => t2TailSlot hk r
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · rcases x with ⟨i, r⟩
      rcases y with ⟨j, s⟩
      fin_cases r <;> fin_cases s <;>
        simp [f, t2PrefixSlot, Fin.ext_iff] at hxy ⊢ <;> omega
    · rcases x with ⟨i, r⟩
      fin_cases r <;> fin_cases y <;>
        simp [f, t2PrefixSlot, t2TailSlot, Fin.ext_iff] at hxy
    · rcases y with ⟨j, s⟩
      fin_cases x <;> fin_cases s <;>
        simp [f, t2PrefixSlot, t2TailSlot, Fin.ext_iff] at hxy
    · fin_cases x <;> fin_cases y <;>
        simp [f, t2TailSlot, Fin.ext_iff] at hxy ⊢ <;> omega
  · intro y
    rcases y with (a | b) | g
    · by_cases hlt : a.val < k - 1
      · refine ⟨Sum.inl (⟨a.val, hlt⟩, 0), ?_⟩
        simp [f, t2PrefixSlot, Fin.ext_iff]
      · have ha : a.val = k - 1 ∨ a.val = k := by omega
        rcases ha with ha | ha
        · refine ⟨Sum.inr 0, ?_⟩
          subst a
          simp [f, t2TailSlot, Fin.ext_iff]
        · refine ⟨Sum.inr 4, ?_⟩
          subst a
          simp [f, t2TailSlot, Fin.ext_iff]
    · by_cases hlt : b.val < k - 1
      · refine ⟨Sum.inl (⟨b.val, hlt⟩, 1), ?_⟩
        simp [f, t2PrefixSlot, Fin.ext_iff]
      · have hb : b.val = k - 1 ∨ b.val = k := by omega
        rcases hb with hb | hb
        · refine ⟨Sum.inr 1, ?_⟩
          subst b
          simp [f, t2TailSlot, Fin.ext_iff]
        · refine ⟨Sum.inr 3, ?_⟩
          subst b
          simp [f, t2TailSlot, Fin.ext_iff]
    · by_cases hlt : g.val < 2 * (k - 1)
      · let j : Fin (k - 1) := ⟨g.val / 2, by omega⟩
        by_cases heven : g.val % 2 = 0
        · refine ⟨Sum.inl (j, 2), ?_⟩
          have hm := Nat.mod_add_div g.val 2
          simp [f, t2PrefixSlot, j, Fin.ext_iff]
          omega
        · have hodd : g.val % 2 = 1 := by
            have hm : g.val % 2 < 2 := Nat.mod_lt _ (by omega)
            omega
          refine ⟨Sum.inl (j, 3), ?_⟩
          have hm := Nat.mod_add_div g.val 2
          simp [f, t2PrefixSlot, j, Fin.ext_iff]
          omega
      · have hg : g.val = 2 * k - 2 ∨ g.val = 2 * k - 1 := by omega
        rcases hg with hg | hg
        · refine ⟨Sum.inr 2, ?_⟩
          subst g
          simp [f, t2TailSlot, Fin.ext_iff]
        · refine ⟨Sum.inr 5, ?_⟩
          subst g
          simp [f, t2TailSlot, Fin.ext_iff]

/-- Canonical pure-index equivalence for the t=2 schedule. -/
def t2IndexEquiv (k : ℕ) (hk : 2 ≤ k) :
    Fin (4 * k + 2) ≃ T2Slots k :=
  (t3BlockTailEquiv k hk).trans (t2RegroupEquiv k hk)

@[simp] theorem t2IndexEquiv_prefix
    (k : ℕ) (hk : 2 ≤ k) (j : Fin (k - 1)) (r : Fin 4) :
    t2IndexEquiv k hk ⟨r.val + 4 * j.val, by omega⟩ =
      t2PrefixSlot j r := by
  simp [t2IndexEquiv, t3BlockTailEquiv, t2RegroupEquiv,
    finProdFinEquiv]
  omega

@[simp] theorem t2IndexEquiv_tail
    (k : ℕ) (hk : 2 ≤ k) (r : Fin 6) :
    t2IndexEquiv k hk ⟨4 * (k - 1) + r.val, by omega⟩ =
      t2TailSlot hk r := by
  simp [t2IndexEquiv, t3BlockTailEquiv, t2RegroupEquiv]
  omega

end

end FiniteSchedule
end HigherRankKUM
