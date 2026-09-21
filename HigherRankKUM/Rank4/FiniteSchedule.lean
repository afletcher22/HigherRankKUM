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
      simp_all [val]
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
  let pos : Fin 2 → Fin n := ![i, j]
  let val : Fin 2 → S := ![⟨x, hx⟩, ⟨y, hy⟩]
  have hpos : Function.Injective pos := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [pos] at hab ⊢
    · exact (hij hab).elim
    · exact (hij hab.symm).elim
  have hval : Function.Injective val := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [val]
  let target : Fin 2 → Fin n := fun r => e₀.symm (val r)
  have htarget : Function.Injective target :=
    e₀.symm.injective.comp hval
  obtain ⟨π, hπ⟩ :=
    Equiv.Perm.exists_extending_pair pos target hpos htarget
  let e : Fin n ≃ S := π.trans e₀
  refine ⟨e, ?_, ?_⟩
  · have h0 : π i = e₀.symm ⟨x, hx⟩ := by
      simpa [pos, target, val] using hπ (0 : Fin 2)
    change (e₀ (π i) : α) = x
    rw [h0]
    simp
  · have h1 : π j = e₀.symm ⟨y, hy⟩ := by
      simpa [pos, target, val] using hπ (1 : Fin 2)
    change (e₀ (π j) : α) = y
    rw [h1]
    simp

/-- Slot type for the t=2 schedule: A-slots, B-slots, and 2k core slots. -/
abbrev T2Slots (k : ℕ) :=
  (Fin (k + 1) ⊕ Fin (k + 1)) ⊕ Fin (2 * k)

def t2PrefixSlot {k : ℕ} (j : Fin (k - 1)) : Fin 4 → T2Slots k :=
  ![Sum.inl (Sum.inl ⟨j.val, by omega⟩),
    Sum.inl (Sum.inr ⟨j.val, by omega⟩),
    Sum.inr ⟨2 * j.val, by omega⟩,
    Sum.inr ⟨2 * j.val + 1, by omega⟩]

def t2TailSlot {k : ℕ} (hk : 2 ≤ k) : Fin 6 → T2Slots k :=
  ![Sum.inl (Sum.inl ⟨k - 1, by omega⟩),
    Sum.inl (Sum.inr ⟨k - 1, by omega⟩),
    Sum.inr ⟨2 * k - 2, by omega⟩,
    Sum.inl (Sum.inr ⟨k, by omega⟩),
    Sum.inl (Sum.inl ⟨k, by omega⟩),
    Sum.inr ⟨2 * k - 1, by omega⟩]

/-- Regroup the t=2 block-plus-tail positions into A,B,G local slots. -/
def t2RegroupEquiv (k : ℕ) (hk : 2 ≤ k) :
    (Fin (k - 1) × Fin 4) ⊕ Fin 6 ≃ T2Slots k := by
  let f : (Fin (k - 1) × Fin 4) ⊕ Fin 6 → T2Slots k
    | Sum.inl x => t2PrefixSlot x.1 x.2
    | Sum.inr r => t2TailSlot hk r
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).2
  refine ⟨?_, ?_⟩
  · intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · rcases x with ⟨i, r⟩
      rcases y with ⟨j, s⟩
      fin_cases r <;> fin_cases s <;>
        simp [f, t2PrefixSlot, Fin.ext_iff] at hxy ⊢ <;> omega
    · rcases x with ⟨i, r⟩
      fin_cases r <;> fin_cases y <;>
        simp [f, t2PrefixSlot, t2TailSlot, Fin.ext_iff] at hxy <;> omega
    · rcases y with ⟨j, s⟩
      fin_cases x <;> fin_cases s <;>
        simp [f, t2PrefixSlot, t2TailSlot, Fin.ext_iff] at hxy <;> omega
    · fin_cases x <;> fin_cases y <;>
        simp [f, t2TailSlot, Fin.ext_iff] at hxy ⊢ <;> omega
  · simp [T2Slots]
    omega

/-- Canonical pure-index equivalence for the t=2 schedule. -/
def t2IndexEquiv (k : ℕ) (hk : 2 ≤ k) :
    Fin (4 * k + 2) ≃ T2Slots k :=
  (t3BlockTailEquiv k hk).trans (t2RegroupEquiv k hk)

@[simp] theorem t2IndexEquiv_prefix
    (k : ℕ) (hk : 2 ≤ k) (j : Fin (k - 1)) (r : Fin 4) :
    t2IndexEquiv k hk ⟨r.val + 4 * j.val, by omega⟩ =
      t2PrefixSlot j r := by
  have hbt :
      t3BlockTailEquiv k hk ⟨r.val + 4 * j.val, by omega⟩ =
        Sum.inl (j, r) := by
    apply (t3BlockTailEquiv k hk).symm.injective
    simp
  simp [t2IndexEquiv, hbt, t2RegroupEquiv]

@[simp] theorem t2IndexEquiv_tail
    (k : ℕ) (hk : 2 ≤ k) (r : Fin 6) :
    t2IndexEquiv k hk ⟨4 * (k - 1) + r.val, by omega⟩ =
      t2TailSlot hk r := by
  have hbt :
      t3BlockTailEquiv k hk ⟨4 * (k - 1) + r.val, by omega⟩ =
        Sum.inr r := by
    apply (t3BlockTailEquiv k hk).symm.injective
    simp
  simp [t2IndexEquiv, hbt, t2RegroupEquiv]





/-- Enumerate a finite set while prescribing three pairwise-distinct
positions and three pairwise-distinct values. -/
theorem exists_fin_equiv_with_three_slots
    {S : Set α} {n : ℕ}
    (hS : S.Finite) (hcard : S.ncard = n)
    (i j l : Fin n)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {x y z : α}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ e : Fin n ≃ S,
      (e i : α) = x ∧ (e j : α) = y ∧ (e l : α) = z := by
  letI : Fintype S := hS.fintype
  have hNatCard : Nat.card S = n := by
    simpa [Nat.card_coe_set_eq] using hcard
  let e₀ : Fin n ≃ S := (Finite.equivFinOfCardEq hNatCard).symm
  let pos : Fin 3 → Fin n := ![i, j, l]
  let val : Fin 3 → S := ![⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩]
  have hpos : Function.Injective pos := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [pos] at hab ⊢
    · exact (hij hab).elim
    · exact (hil hab).elim
    · exact (hij hab.symm).elim
    · exact (hjl hab).elim
    · exact (hil hab.symm).elim
    · exact (hjl hab.symm).elim
  have hval : Function.Injective val := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [val]
  let target : Fin 3 → Fin n := fun r => e₀.symm (val r)
  have htarget : Function.Injective target :=
    e₀.symm.injective.comp hval
  obtain ⟨π, hπ⟩ :=
    Equiv.Perm.exists_extending_pair pos target hpos htarget
  let e : Fin n ≃ S := π.trans e₀
  refine ⟨e, ?_, ?_, ?_⟩
  · have h0 : π i = e₀.symm ⟨x, hx⟩ := by
      simpa [pos, target, val] using hπ (0 : Fin 3)
    change (e₀ (π i) : α) = x
    rw [h0]
    simp
  · have h1 : π j = e₀.symm ⟨y, hy⟩ := by
      simpa [pos, target, val] using hπ (1 : Fin 3)
    change (e₀ (π j) : α) = y
    rw [h1]
    simp
  · have h2 : π l = e₀.symm ⟨z, hz⟩ := by
      simpa [pos, target, val] using hπ (2 : Fin 3)
    change (e₀ (π l) : α) = z
    rw [h2]
    simp

/-- Enumerate a finite set while prescribing three pairwise-distinct
positions and three pairwise-distinct values. -/
theorem exists_fin_equiv_with_three_at_positions
    {S : Set α} {n : ℕ}
    (hS : S.Finite) (hcard : S.ncard = n)
    (i j l : Fin n)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {x y z : α}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ e : Fin n ≃ S,
      (e i : α) = x ∧
      (e j : α) = y ∧
      (e l : α) = z := by
  letI : Fintype S := hS.fintype
  have hNatCard : Nat.card S = n := by
    simpa [Nat.card_coe_set_eq] using hcard
  let e₀ : Fin n ≃ S := (Finite.equivFinOfCardEq hNatCard).symm
  let pos : Fin 3 → Fin n := ![i, j, l]
  let val : Fin 3 → S := ![⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩]
  have hpos : Function.Injective pos := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [pos]
  have hval : Function.Injective val := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [val]
  let target : Fin 3 → Fin n := fun r => e₀.symm (val r)
  have htarget : Function.Injective target :=
    e₀.symm.injective.comp hval
  obtain ⟨π, hπ⟩ :=
    Equiv.Perm.exists_extending_pair pos target hpos htarget
  let e : Fin n ≃ S := π.trans e₀
  refine ⟨e, ?_, ?_, ?_⟩
  · have hi : π i = e₀.symm ⟨x, hx⟩ := by
      simpa [pos, target, val] using hπ (0 : Fin 3)
    change (e₀ (π i) : α) = x
    rw [hi]
    simp
  · have hj : π j = e₀.symm ⟨y, hy⟩ := by
      simpa [pos, target, val] using hπ (1 : Fin 3)
    change (e₀ (π j) : α) = y
    rw [hj]
    simp
  · have hl : π l = e₀.symm ⟨z, hz⟩ := by
      simpa [pos, target, val] using hπ (2 : Fin 3)
    change (e₀ (π l) : α) = z
    rw [hl]
    simp

/-! ### Compressed dangerous-hyperplane schedules -/

/-- Slot type for the unified dangerous-hyperplane construction:
k+1 complement slots and 3k+1 core slots. -/
abbrev HyperplaneSlots (k : ℕ) :=
  Fin (k + 1) ⊕ Fin (3 * k + 1)

/-- Ordinary block of the adjacent-good schedule (C G G G)^k C G. -/
def hyperAdjacentBlockSlot {k : ℕ} (j : Fin k) : Fin 4 → HyperplaneSlots k :=
  ![Sum.inl ⟨j.val, by omega⟩,
    Sum.inr ⟨3 * j.val, by omega⟩,
    Sum.inr ⟨3 * j.val + 1, by omega⟩,
    Sum.inr ⟨3 * j.val + 2, by omega⟩]

/-- Two-position tail of the adjacent-good schedule. -/
def hyperAdjacentTailSlot {k : ℕ} : Fin 2 → HyperplaneSlots k :=
  ![Sum.inl ⟨k, by omega⟩,
    Sum.inr ⟨3 * k, by omega⟩]

/-- Regroup k four-blocks and a two-position tail into complement/core
slots for the adjacent-good schedule. -/
def hyperAdjacentRegroupEquiv (k : ℕ) (hk : 1 ≤ k) :
    (Fin k × Fin 4) ⊕ Fin 2 ≃ HyperplaneSlots k := by
  let f : (Fin k × Fin 4) ⊕ Fin 2 → HyperplaneSlots k
    | Sum.inl x => hyperAdjacentBlockSlot x.1 x.2
    | Sum.inr r => hyperAdjacentTailSlot r
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).2
  refine ⟨?_, ?_⟩
  · intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · rcases x with ⟨i, r⟩
      rcases y with ⟨j, s⟩
      fin_cases r <;> fin_cases s <;>
        simp [f, hyperAdjacentBlockSlot, Fin.ext_iff] at hxy ⊢ <;> omega
    · rcases x with ⟨i, r⟩
      fin_cases r <;> fin_cases y <;>
        simp [f, hyperAdjacentBlockSlot, hyperAdjacentTailSlot,
          Fin.ext_iff] at hxy <;> omega
    · rcases y with ⟨j, s⟩
      fin_cases x <;> fin_cases s <;>
        simp [f, hyperAdjacentBlockSlot, hyperAdjacentTailSlot,
          Fin.ext_iff] at hxy <;> omega
    · fin_cases x <;> fin_cases y <;>
        simp [f, hyperAdjacentTailSlot, Fin.ext_iff] at hxy ⊢
  · simp [HyperplaneSlots]
    omega

/-- Decompose the adjacent-good schedule into k four-blocks and a
two-position tail. -/
def hyperAdjacentBlockTailEquiv (k : ℕ) (hk : 1 ≤ k) :
    Fin (4 * k + 2) ≃ (Fin k × Fin 4) ⊕ Fin 2 := by
  have hcard : k * 4 + 2 = 4 * k + 2 := by omega
  exact (finCongr hcard.symm).trans
    ((finSumFinEquiv :
      Fin (k * 4) ⊕ Fin 2 ≃ Fin (k * 4 + 2)).symm.trans
      (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _)))

def hyperAdjacentIndexEquiv (k : ℕ) (hk : 1 ≤ k) :
    Fin (4 * k + 2) ≃ HyperplaneSlots k :=
  (hyperAdjacentBlockTailEquiv k hk).trans (hyperAdjacentRegroupEquiv k hk)

@[simp] theorem hyperAdjacentBlockTailEquiv_symm_block
    (k : ℕ) (hk : 1 ≤ k) (j : Fin k) (r : Fin 4) :
    (hyperAdjacentBlockTailEquiv k hk).symm (Sum.inl (j, r)) =
      ⟨r.val + 4 * j.val, by omega⟩ := by
  apply Fin.ext
  simp [hyperAdjacentBlockTailEquiv, finProdFinEquiv]

@[simp] theorem hyperAdjacentBlockTailEquiv_symm_tail
    (k : ℕ) (hk : 1 ≤ k) (r : Fin 2) :
    (hyperAdjacentBlockTailEquiv k hk).symm (Sum.inr r) =
      ⟨4 * k + r.val, by omega⟩ := by
  apply Fin.ext
  simp [hyperAdjacentBlockTailEquiv]

@[simp] theorem hyperAdjacentIndexEquiv_block
    (k : ℕ) (hk : 1 ≤ k) (j : Fin k) (r : Fin 4) :
    hyperAdjacentIndexEquiv k hk ⟨r.val + 4 * j.val, by omega⟩ =
      hyperAdjacentBlockSlot j r := by
  have hbt :
      hyperAdjacentBlockTailEquiv k hk ⟨r.val + 4 * j.val, by omega⟩ =
        Sum.inl (j, r) := by
    apply (hyperAdjacentBlockTailEquiv k hk).symm.injective
    simp
  simp [hyperAdjacentIndexEquiv, hbt, hyperAdjacentRegroupEquiv]

@[simp] theorem hyperAdjacentIndexEquiv_tail
    (k : ℕ) (hk : 1 ≤ k) (r : Fin 2) :
    hyperAdjacentIndexEquiv k hk ⟨4 * k + r.val, by omega⟩ =
      hyperAdjacentTailSlot r := by
  have hbt :
      hyperAdjacentBlockTailEquiv k hk ⟨4 * k + r.val, by omega⟩ =
        Sum.inr r := by
    apply (hyperAdjacentBlockTailEquiv k hk).symm.injective
    simp
  simp [hyperAdjacentIndexEquiv, hbt, hyperAdjacentRegroupEquiv]

/-- Six-position head of the separated-good schedule
C G G C G G (C G G G)^(k-1). -/
def hyperSeparatedHeadSlot {k : ℕ} (hk : 2 ≤ k) :
    Fin 6 → HyperplaneSlots k :=
  ![Sum.inl ⟨0, by omega⟩,
    Sum.inr ⟨0, by omega⟩,
    Sum.inr ⟨1, by omega⟩,
    Sum.inl ⟨1, by omega⟩,
    Sum.inr ⟨2, by omega⟩,
    Sum.inr ⟨3, by omega⟩]

/-- Repeated four-blocks following the six-position head in the
separated-good schedule. -/
def hyperSeparatedBlockSlot {k : ℕ} (hk : 2 ≤ k)
    (j : Fin (k - 1)) : Fin 4 → HyperplaneSlots k :=
  ![Sum.inl ⟨j.val + 2, by omega⟩,
    Sum.inr ⟨3 * j.val + 4, by omega⟩,
    Sum.inr ⟨3 * j.val + 5, by omega⟩,
    Sum.inr ⟨3 * j.val + 6, by omega⟩]

/-- Regroup the separated-good head and repeated blocks into complement/core
slots. -/
def hyperSeparatedRegroupEquiv (k : ℕ) (hk : 2 ≤ k) :
    Fin 6 ⊕ (Fin (k - 1) × Fin 4) ≃ HyperplaneSlots k := by
  let f : Fin 6 ⊕ (Fin (k - 1) × Fin 4) → HyperplaneSlots k
    | Sum.inl r => hyperSeparatedHeadSlot hk r
    | Sum.inr x => hyperSeparatedBlockSlot hk x.1 x.2
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).2
  refine ⟨?_, ?_⟩
  · intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · fin_cases x <;> fin_cases y <;>
        simp [f, hyperSeparatedHeadSlot, Fin.ext_iff] at hxy ⊢ <;> omega
    · rcases y with ⟨j, s⟩
      fin_cases x <;> fin_cases s <;>
        simp [f, hyperSeparatedHeadSlot, hyperSeparatedBlockSlot,
          Fin.ext_iff] at hxy <;> omega
    · rcases x with ⟨i, r⟩
      fin_cases r <;> fin_cases y <;>
        simp [f, hyperSeparatedHeadSlot, hyperSeparatedBlockSlot,
          Fin.ext_iff] at hxy <;> omega
    · rcases x with ⟨i, r⟩
      rcases y with ⟨j, s⟩
      fin_cases r <;> fin_cases s <;>
        simp [f, hyperSeparatedBlockSlot, Fin.ext_iff] at hxy ⊢ <;> omega
  · simp [HyperplaneSlots]
    omega

/-- Decompose the separated-good schedule into a six-position head followed
by k-1 four-blocks. -/
def hyperSeparatedHeadBlockEquiv (k : ℕ) (hk : 2 ≤ k) :
    Fin (4 * k + 2) ≃ Fin 6 ⊕ (Fin (k - 1) × Fin 4) := by
  have hcard : 6 + (k - 1) * 4 = 4 * k + 2 := by omega
  exact (finCongr hcard.symm).trans
    ((finSumFinEquiv :
      Fin 6 ⊕ Fin ((k - 1) * 4) ≃ Fin (6 + (k - 1) * 4)).symm.trans
      (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv.symm))

def hyperSeparatedIndexEquiv (k : ℕ) (hk : 2 ≤ k) :
    Fin (4 * k + 2) ≃ HyperplaneSlots k :=
  (hyperSeparatedHeadBlockEquiv k hk).trans
    (hyperSeparatedRegroupEquiv k hk)

@[simp] theorem hyperSeparatedHeadBlockEquiv_symm_head
    (k : ℕ) (hk : 2 ≤ k) (r : Fin 6) :
    (hyperSeparatedHeadBlockEquiv k hk).symm (Sum.inl r) =
      ⟨r.val, by omega⟩ := by
  apply Fin.ext
  simp [hyperSeparatedHeadBlockEquiv]

@[simp] theorem hyperSeparatedHeadBlockEquiv_symm_block
    (k : ℕ) (hk : 2 ≤ k) (j : Fin (k - 1)) (r : Fin 4) :
    (hyperSeparatedHeadBlockEquiv k hk).symm (Sum.inr (j, r)) =
      ⟨6 + r.val + 4 * j.val, by omega⟩ := by
  apply Fin.ext
  simp [hyperSeparatedHeadBlockEquiv, finProdFinEquiv]
  omega

@[simp] theorem hyperSeparatedIndexEquiv_head
    (k : ℕ) (hk : 2 ≤ k) (r : Fin 6) :
    hyperSeparatedIndexEquiv k hk ⟨r.val, by omega⟩ =
      hyperSeparatedHeadSlot hk r := by
  have hbt :
      hyperSeparatedHeadBlockEquiv k hk ⟨r.val, by omega⟩ =
        Sum.inl r := by
    apply (hyperSeparatedHeadBlockEquiv k hk).symm.injective
    simp
  simp [hyperSeparatedIndexEquiv, hbt, hyperSeparatedRegroupEquiv]

@[simp] theorem hyperSeparatedIndexEquiv_block
    (k : ℕ) (hk : 2 ≤ k) (j : Fin (k - 1)) (r : Fin 4) :
    hyperSeparatedIndexEquiv k hk
        ⟨6 + r.val + 4 * j.val, by omega⟩ =
      hyperSeparatedBlockSlot hk j r := by
  have hbt :
      hyperSeparatedHeadBlockEquiv k hk
          ⟨6 + r.val + 4 * j.val, by omega⟩ =
        Sum.inr (j, r) := by
    apply (hyperSeparatedHeadBlockEquiv k hk).symm.injective
    simp
  simp [hyperSeparatedIndexEquiv, hbt, hyperSeparatedRegroupEquiv]

@[simp] theorem hyperSeparatedIndexEquiv_head0
    (k : ℕ) (hk : 2 ≤ k) :
    hyperSeparatedIndexEquiv k hk ⟨0, by omega⟩ =
      Sum.inl ⟨0, by omega⟩ := by
  simpa [hyperSeparatedHeadSlot] using
    hyperSeparatedIndexEquiv_head k hk (0 : Fin 6)

@[simp] theorem hyperSeparatedIndexEquiv_head1
    (k : ℕ) (hk : 2 ≤ k) :
    hyperSeparatedIndexEquiv k hk ⟨1, by omega⟩ =
      Sum.inr ⟨0, by omega⟩ := by
  simpa [hyperSeparatedHeadSlot] using
    hyperSeparatedIndexEquiv_head k hk (1 : Fin 6)

@[simp] theorem hyperSeparatedIndexEquiv_head2
    (k : ℕ) (hk : 2 ≤ k) :
    hyperSeparatedIndexEquiv k hk ⟨2, by omega⟩ =
      Sum.inr ⟨1, by omega⟩ := by
  simpa [hyperSeparatedHeadSlot] using
    hyperSeparatedIndexEquiv_head k hk (2 : Fin 6)

@[simp] theorem hyperSeparatedIndexEquiv_head3
    (k : ℕ) (hk : 2 ≤ k) :
    hyperSeparatedIndexEquiv k hk ⟨3, by omega⟩ =
      Sum.inl ⟨1, by omega⟩ := by
  simpa [hyperSeparatedHeadSlot] using
    hyperSeparatedIndexEquiv_head k hk (3 : Fin 6)

@[simp] theorem hyperSeparatedIndexEquiv_head4
    (k : ℕ) (hk : 2 ≤ k) :
    hyperSeparatedIndexEquiv k hk ⟨4, by omega⟩ =
      Sum.inr ⟨2, by omega⟩ := by
  simpa [hyperSeparatedHeadSlot] using
    hyperSeparatedIndexEquiv_head k hk (4 : Fin 6)

@[simp] theorem hyperSeparatedIndexEquiv_head5
    (k : ℕ) (hk : 2 ≤ k) :
    hyperSeparatedIndexEquiv k hk ⟨5, by omega⟩ =
      Sum.inr ⟨3, by omega⟩ := by
  simpa [hyperSeparatedHeadSlot] using
    hyperSeparatedIndexEquiv_head k hk (5 : Fin 6)

end

end FiniteSchedule
end HigherRankKUM
