import Probe.XP.Basic
import HigherRankKUM.CyclicOrder

/-!
# Pair-chain insertion (XP): cycles and chains

* `cycle_sat`: **the cycle lemma.** A cyclic sequence of relations on `Bool × Bool` in which
  every row is nonempty and one relation is `Slack` is satisfiable. Walk around the cycle from the
  slack relation, and close it there (`slack_close`).
* `orient_odd`: the same for the relations `W i` linking `o i` and `o (i + 2)` on `ℤ/n`, `n` odd
  (one cycle `0, 2, …, n - 1, 1, 3, …, n - 2`).
* `cbo_of_chain`: **an oriented pair chain is a cyclic basis ordering.** Pairs `B i` (`i < n`,
  periodic), orientations `o i`; if every `B i ∪ B (i+1)` and every window
  `{last B i} ∪ B (i+1) ∪ {first B (i+2)}` is a basis, then reading first, last, first, last, …
  is a cyclic basis ordering of `M`.
-/

namespace HigherRankKUM.XP

open Set

variable {α : Type*}

/-! ### The cycle lemma -/

theorem mod_succ_cases {t L : ℕ} (ht : t < L) :
    ((t + 1) % L = t + 1 ∧ t + 1 < L) ∨ ((t + 1) % L = 0 ∧ t + 1 = L) := by
  rcases Nat.lt_or_ge (t + 1) L with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · have e : t + 1 = L := by omega
    refine Or.inr ⟨?_, e⟩
    rw [e, Nat.mod_self]

/-- Iterating a step function from `c`. -/
def iterStep (step : ℕ → Bool → Bool) (c : Bool) : ℕ → Bool
  | 0 => c
  | s + 1 => step s (iterStep step c s)

theorem iterStep_succ (step : ℕ → Bool → Bool) (c : Bool) (s : ℕ) :
    iterStep step c (s + 1) = step s (iterStep step c s) := rfl

theorem iterStep_zero (step : ℕ → Bool → Bool) (c : Bool) : iterStep step c 0 = c := rfl

/-- The offset of position `t` after the position `k + 1`, on a cycle of length `L`. -/
def cyclePos (L k t : ℕ) : ℕ := if k < t then t - k - 1 else t + L - k - 1

/-- **The cycle lemma.** -/
theorem cycle_sat {L : ℕ} (R : ℕ → Bool → Bool → Prop) (hrow : ∀ t < L, ∀ x, ∃ y, R t x y)
    {k : ℕ} (hk : k < L) (hslack : Slack (R k)) :
    ∃ x : ℕ → Bool, ∀ t < L, R t (x t) (x ((t + 1) % L)) := by
  have hrow' : ∀ s x, ∃ y, R ((k + 1 + s) % L) x y := fun s x =>
    hrow _ (Nat.mod_lt _ (by omega)) x
  let step : ℕ → Bool → Bool := fun s x => Classical.choose (hrow' s x)
  have hstep : ∀ s x, R ((k + 1 + s) % L) x (step s x) := fun s x =>
    Classical.choose_spec (hrow' s x)
  obtain ⟨c, hc⟩ := slack_close hslack (fun c => iterStep step c (L - 1))
  refine ⟨fun t => iterStep step c (cyclePos L k t), fun t ht => ?_⟩
  show R t (iterStep step c (cyclePos L k t)) (iterStep step c (cyclePos L k ((t + 1) % L)))
  by_cases htk : t = k
  · rw [htk]
    have h1 : cyclePos L k k = L - 1 := by
      unfold cyclePos
      rw [ite_eq_right (lt_irrefl k)]
      omega
    have h2 : cyclePos L k ((k + 1) % L) = 0 := by
      rcases mod_succ_cases hk with ⟨he, -⟩ | ⟨he, heq⟩
      · rw [he]
        unfold cyclePos
        split_ifs <;> omega
      · rw [he]
        unfold cyclePos
        split_ifs <;> omega
    rw [h1, h2, iterStep_zero]
    exact hc
  · have h1 : cyclePos L k ((t + 1) % L) = cyclePos L k t + 1 := by
      rcases mod_succ_cases ht with ⟨he, -⟩ | ⟨he, heq⟩
      · rw [he]
        unfold cyclePos
        split_ifs <;> omega
      · rw [he]
        unfold cyclePos
        split_ifs <;> omega
    have h2 : (k + 1 + cyclePos L k t) % L = t := by
      unfold cyclePos
      split_ifs with hkt
      · rw [show k + 1 + (t - k - 1) = t by omega, Nat.mod_eq_of_lt ht]
      · rw [show k + 1 + (t + L - k - 1) = t + L by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt ht]
    rw [h1, iterStep_succ]
    have := hstep (cyclePos L k t) (iterStep step c (cyclePos L k t))
    rw [h2] at this
    exact this

/-! ### Relations `o i → o (i + 2)` on an odd cycle -/

/-- The position of `i` on the cycle `0, 2, …, n - 1, 1, 3, …, n - 2`. -/
def oddPos (n i : ℕ) : ℕ := if i % 2 = 0 then i / 2 else (n + i) / 2

/-- The index at position `t` of that cycle. -/
def oddIdx (n t : ℕ) : ℕ := if 2 * t < n then 2 * t else 2 * t - n

theorem orient_odd {n : ℕ} (hn : n % 2 = 1) (hn3 : 3 ≤ n) (W : ℕ → Bool → Bool → Prop)
    (hrow : ∀ i < n, ∀ x, ∃ y, W i x y) {k : ℕ} (hk : k < n) (hslack : Slack (W k)) :
    ∃ o : ℕ → Bool, ∀ i < n, W i (o i) (o ((i + 2) % n)) := by
  have hidx : ∀ t < n, oddIdx n t < n := by
    intro t ht
    unfold oddIdx
    split_ifs <;> omega
  have hpos : ∀ i < n, oddPos n i < n := by
    intro i hi
    unfold oddPos
    split_ifs <;> omega
  have hinv : ∀ i < n, oddIdx n (oddPos n i) = i := by
    intro i hi
    unfold oddPos oddIdx
    split_ifs <;> omega
  have hsucc : ∀ i < n, oddPos n ((i + 2) % n) = (oddPos n i + 1) % n := by
    intro i hi
    rcases Nat.lt_or_ge (i + 2) n with h | h
    · have h1 : oddPos n i + 1 < n := by
        unfold oddPos
        split_ifs <;> omega
      rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt h1]
      unfold oddPos
      split_ifs <;> omega
    · rcases (show i + 2 = n ∨ i + 2 = n + 1 by omega) with h2 | h2
      · have h1 : oddPos n i + 1 = n := by
          unfold oddPos
          split_ifs <;> omega
        rw [h2, Nat.mod_self, h1, Nat.mod_self]
        unfold oddPos
        split_ifs <;> omega
      · have h1 : oddPos n i + 1 < n := by
          unfold oddPos
          split_ifs <;> omega
        have h3 : (i + 2) % n = 1 := by
          rw [h2, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt (by omega)
        rw [h3, Nat.mod_eq_of_lt h1]
        unfold oddPos
        split_ifs <;> omega
  obtain ⟨x, hx⟩ := cycle_sat (L := n) (fun t => W (oddIdx n t))
    (fun t ht => hrow _ (hidx t ht)) (hpos k hk)
    (by show Slack (W (oddIdx n (oddPos n k))); rw [hinv k hk]; exact hslack)
  refine ⟨fun i => x (oddPos n i), fun i hi => ?_⟩
  have h : W (oddIdx n (oddPos n i)) (x (oddPos n i)) (x ((oddPos n i + 1) % n)) :=
    hx (oddPos n i) (hpos i hi)
  rw [hinv i hi] at h
  show W i (x (oddPos n i)) (x (oddPos n ((i + 2) % n)))
  rw [hsucc i hi]
  exact h

/-! ### From an oriented pair chain to a cyclic basis ordering -/

/-- The sequence first, last, first, last, … of an oriented pair chain. -/
def chainSeq (B : ℕ → Bool → α) (o : ℕ → Bool) (p : ℕ) : α :=
  B (p / 2) (if p % 2 = 0 then o (p / 2) else !o (p / 2))

theorem chainSeq_even (B : ℕ → Bool → α) (o : ℕ → Bool) (i : ℕ) :
    chainSeq B o (2 * i) = B i (o i) := by
  unfold chainSeq
  rw [show 2 * i / 2 = i by omega, ite_eq_left (by omega)]

theorem chainSeq_odd (B : ℕ → Bool → α) (o : ℕ → Bool) (i : ℕ) :
    chainSeq B o (2 * i + 1) = B i (!o i) := by
  unfold chainSeq
  rw [show (2 * i + 1) / 2 = i by omega, ite_eq_right (by omega)]

/-- **An oriented pair chain is a cyclic basis ordering.** -/
theorem cbo_of_chain {M : Matroid α} {n : ℕ} (hn : 0 < n) (B : ℕ → Bool → α) (o : ℕ → Bool)
    (hB : ∀ i, B (i + n) = B i) (ho : ∀ i, o (i + n) = o i)
    (hmem : ∀ i b, B i b ∈ M.E) (hsurj : ∀ x ∈ M.E, ∃ i < n, ∃ b, B i b = x)
    (hcard : M.E.ncard = 2 * n)
    (heven : ∀ i < n, M.IsBase {B i false, B i true, B (i + 1) false, B (i + 1) true})
    (hodd : ∀ i < n,
      M.IsBase {B i (!o i), B (i + 1) false, B (i + 1) true, B (i + 2) (o (i + 2))}) :
    ∃ τ : Fin (2 * n) ≃ M.E, CyclicBasisOrder M 4 (by omega) τ := by
  have h2n : 0 < 2 * n := by omega
  -- periodicity of the sequence
  have hg1 : ∀ p, chainSeq B o (p + 2 * n) = chainSeq B o p := by
    intro p
    unfold chainSeq
    rw [show (p + 2 * n) / 2 = p / 2 + n by omega, show (p + 2 * n) % 2 = p % 2 by omega, hB, ho]
  have hgq : ∀ p q, chainSeq B o (p + 2 * n * q) = chainSeq B o p := by
    intro p q
    induction q with
    | zero => simp
    | succ q ih => rw [show p + 2 * n * (q + 1) = (p + 2 * n * q) + 2 * n by ring, hg1, ih]
  have hgper : ∀ p, chainSeq B o (p % (2 * n)) = chainSeq B o p := by
    intro p
    conv_rhs => rw [← Nat.mod_add_div p (2 * n)]
    rw [hgq]
  -- the numbering
  let f : Fin (2 * n) → M.E := fun p => ⟨chainSeq B o p, hmem _ _⟩
  have hfs : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, b, rfl⟩ := hsurj x hx
    by_cases hb : b = o i
    · refine ⟨⟨2 * i, by omega⟩, Subtype.ext ?_⟩
      show chainSeq B o (2 * i) = B i b
      rw [chainSeq_even, hb]
    · refine ⟨⟨2 * i + 1, by omega⟩, Subtype.ext ?_⟩
      show chainSeq B o (2 * i + 1) = B i b
      rw [chainSeq_odd]
      congr 1
      cases b <;> cases hoi : o i <;> simp_all
  have hfb : Function.Bijective f := hfs.bijective_of_nat_card_le (by simp [hcard])
  refine ⟨Equiv.ofBijective f hfb, fun p => ?_⟩
  have hwin : cyclicWindow 4 h2n (Equiv.ofBijective f hfb) p =
      {chainSeq B o p, chainSeq B o (p + 1), chainSeq B o (p + 2), chainSeq B o (p + 3)} := by
    have hval : ∀ j : ℕ, ((Equiv.ofBijective f hfb (cyclicIndex (2 * n) h2n p j) : M.E) : α) =
        chainSeq B o (p + j) := by
      intro j
      show chainSeq B o (((p : ℕ) + j) % (2 * n)) = _
      rw [hgper]
    ext x
    simp only [cyclicWindow, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, hval]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨3, by simp⟩
  rw [hwin]
  obtain ⟨i, hi | hi⟩ : ∃ i, (p : ℕ) = 2 * i ∨ (p : ℕ) = 2 * i + 1 := ⟨(p : ℕ) / 2, by omega⟩
  · have hin : i < n := by omega
    rw [hi, show 2 * i + 2 = 2 * (i + 1) by ring, show 2 * i + 3 = 2 * (i + 1) + 1 by ring,
      chainSeq_even B o i, chainSeq_odd B o i, chainSeq_even B o (i + 1),
      chainSeq_odd B o (i + 1), pair_set_eq (B i) (B (i + 1)) (o i) (o (i + 1))]
    exact heven i hin
  · have hin : i < n := by omega
    rw [hi, show 2 * i + 1 + 1 = 2 * (i + 1) by ring,
      show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring, show 2 * i + 1 + 3 = 2 * (i + 2) by ring,
      chainSeq_odd B o i, chainSeq_even B o (i + 1), chainSeq_odd B o (i + 1),
      chainSeq_even B o (i + 2), win_set_eq (B i (!o i)) (B (i + 2) (o (i + 2))) (B (i + 1))
        (o (i + 1))]
    exact hodd i hin

end HigherRankKUM.XP
