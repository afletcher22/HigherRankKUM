import Probe.XP.Local
import Probe.XP.Chain
import Probe.Rank4.TheoremD

/-!
# Pair-chain insertion (XP): the rank-4 extension theorem for even `N ≥ 8`

Let `S` be a basis of a rank-4 matroid `M`, and `σ = e₀ … e_{N-1}` a cyclic basis ordering of
`M \ S`, `N = 2m`, `m ≥ 4`. The pairs `A_i = (e_{2i}, e_{2i+1})` form an oriented pair chain
(`OldChain`), with relations `R_k = oldR M A k` from `A_k` to `A_{k+2}` through `A_{k+1}`.

After a rotation by `r` pairs, insert a split `(P, Q)` of `S` after the old pair `m - 1 + r`. The
new chain `newChain m r A P Q` has `m + 2` pairs, and its window relations are `newW`: the old
relations `R_{i+r}` for `i + 2 < m`, and the four local windows `Wa, Wb, Wc, Wd` at
`i = m - 2, m - 1, m, m + 1`. The steps `i → i + 2` form one cycle (`m` odd) or two (`m` even).

* A cycle that keeps a slack old relation is oriented by the cycle lemma (`orient_odd`,
  `cycle_sat`). The split is the Greene–Magnanti split of the local lemma.
* A cycle whose old relations are all tight is oriented by flipping whole paths (`tightO`,
  `mixO`); its new windows come from the local lemma (`local_at`).
* The rotation `r` is chosen so that this covers every case (`choice_even`): with `m` odd, a
  slack relation is put at `m - 3`; with `m` even, a slack relation is put at `m - 3` (in the
  cycle through `Q`), and the cycle through `P` keeps a slack relation or is tight.

`cbo_of_chain` turns the oriented new chain into a cyclic basis ordering of `M`
(`rank4Extension_of_even`).
-/

namespace HigherRankKUM.XP

open Set

variable {α : Type*} {M : Matroid α}

/-! ### Old chains -/

/-- The relation `R_k`: `{last A_k} ∪ A_{k+1} ∪ {first A_{k+2}}` is a basis, for orientations `x`
of `A_k` and `y` of `A_{k+2}`. -/
def oldR (M : Matroid α) (A : ℕ → Bool → α) (k : ℕ) (x y : Bool) : Prop :=
  M.IsBase {A k (!x), A (k + 1) false, A (k + 1) true, A (k + 2) y}

/-- A cyclic chain of `m` pairs whose `σ`-orientation is a cyclic basis ordering, avoiding
`S`. -/
structure OldChain (M : Matroid α) (m : ℕ) (A : ℕ → Bool → α) (S : Set α) : Prop where
  per : ∀ k, A (k + m) = A k
  even : ∀ k, M.IsBase {A k false, A k true, A (k + 1) false, A (k + 1) true}
  odd : ∀ k, oldR M A k false false
  notS : ∀ k b, A k b ∉ S

namespace OldChain

variable {m : ℕ} {A : ℕ → Bool → α} {S : Set α}

theorem mem (h : OldChain M m A S) (k : ℕ) (b : Bool) : A k b ∈ M.E := by
  cases b
  · exact (h.even k).subset_ground (by simp)
  · exact (h.even k).subset_ground (by simp)

theorem even2 (h : OldChain M m A S) (k : ℕ) :
    M.IsBase {A (k + 1) false, A (k + 1) true, A (k + 2) false, A (k + 2) true} := by
  have h1 := h.even (k + 1)
  rwa [show k + 1 + 1 = k + 2 by omega] at h1

theorem perR (h : OldChain M m A S) (k : ℕ) : oldR M A (k + m) = oldR M A k := by
  funext x y
  unfold oldR
  rw [show k + m + 1 = k + 1 + m by omega, show k + m + 2 = k + 2 + m by omega, h.per, h.per,
    h.per]

/-- Rows of `R_k` are nonempty. -/
theorem row (hRank : M.eRank = 4) (h : OldChain M m A S) (k : ℕ) (x : Bool) :
    oldR M A k x false ∨ oldR M A k x true := by
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank (h.even k)
  unfold oldR
  cases x <;> simp only [Bool.not_false, Bool.not_true] <;>
    exact exists_isBase_augment hRank ((h.even k).indep.subset (by sub_perm)) (by ne_tac)
      (by ne_tac) (by ne_tac) (h.even2 k)

/-- Columns of `R_k` are nonempty. -/
theorem col (hRank : M.eRank = 4) (h : OldChain M m A S) (k : ℕ) (y : Bool) :
    oldR M A k false y ∨ oldR M A k true y := by
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank (h.even2 k)
  unfold oldR
  simp only [Bool.not_false, Bool.not_true]
  have hI : M.Indep {A (k + 1) false, A (k + 1) true, A (k + 2) y} :=
    (h.even2 k).indep.subset (by cases y <;> sub_perm)
  exact (exists_isBase_augment_first hRank hI (by ne_tac) (by cases y <;> ne_tac)
    (by cases y <;> ne_tac) (h.even k)).symm

/-- A tight relation (not slack) is the identity. -/
theorem tt_of_tight (hRank : M.eRank = 4) (h : OldChain M m A S) (k : ℕ)
    (ht : ¬ Slack (oldR M A k)) :
    oldR M A k true true ∧ ¬ oldR M A k false true ∧ ¬ oldR M A k true false := by
  have h1 := tight_of_not_slack (h.odd k) (h.row hRank k true) (h.col hRank k true) ht
  exact ⟨(h.row hRank k true).resolve_left h1.2, h1.1, h1.2⟩

end OldChain

/-! ### The new chain -/

/-- Pair `j` of the new chain: old pairs `r, …, m - 1 + r`, then `P`, then `Q`. -/
def newPair (m r : ℕ) (A : ℕ → Bool → α) (P Q : Bool → α) (j : ℕ) : Bool → α :=
  if j < m then A (j + r) else if j = m then P else Q

/-- The new chain, periodic with period `m + 2`. -/
def newChain (m r : ℕ) (A : ℕ → Bool → α) (P Q : Bool → α) (i : ℕ) : Bool → α :=
  newPair m r A P Q (i % (m + 2))

/-- The window relations of the new chain. -/
def newW (M : Matroid α) (m r : ℕ) (A : ℕ → Bool → α) (P Q : Bool → α) (i : ℕ)
    (x y : Bool) : Prop :=
  M.IsBase {newChain m r A P Q i (!x), newChain m r A P Q (i + 1) false,
    newChain m r A P Q (i + 1) true, newChain m r A P Q (i + 2) y}

section NewChain

variable {m r : ℕ} {A : ℕ → Bool → α} {P Q : Bool → α}

theorem nc_A {i j : ℕ} (hi : i < m) (hj : j = i + r) : newChain m r A P Q i = A j := by
  unfold newChain newPair
  rw [Nat.mod_eq_of_lt (by omega : i < m + 2), if_pos hi, hj]

theorem nc_P : newChain m r A P Q m = P := by
  unfold newChain newPair
  rw [Nat.mod_eq_of_lt (by omega : m < m + 2), if_neg (lt_irrefl m), if_pos rfl]

theorem nc_Q : newChain m r A P Q (m + 1) = Q := by
  unfold newChain newPair
  rw [Nat.mod_eq_of_lt (by omega : m + 1 < m + 2), if_neg (by omega), if_neg (by omega)]

theorem nc_A0 (hm : 0 < m) : newChain m r A P Q (m + 2) = A r := by
  unfold newChain newPair
  rw [Nat.mod_self, if_pos hm, Nat.zero_add]

theorem nc_A1 (hm : 1 < m) : newChain m r A P Q (m + 3) = A (1 + r) := by
  unfold newChain newPair
  rw [show m + 3 = (m + 2) + 1 by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (by omega : 1 < m + 2), if_pos hm]

theorem nc_per (i : ℕ) : newChain m r A P Q (i + (m + 2)) = newChain m r A P Q i := by
  unfold newChain
  rw [Nat.add_mod_right]

theorem nc_mod (i : ℕ) : newChain m r A P Q (i % (m + 2)) = newChain m r A P Q i := by
  unfold newChain
  rw [Nat.mod_mod]

theorem nc_succ_mod (i : ℕ) :
    newChain m r A P Q (i % (m + 2) + 1) = newChain m r A P Q (i + 1) := by
  unfold newChain
  rw [Nat.mod_add_mod]

theorem newW_old {i : ℕ} (hi : i + 2 < m) : newW M m r A P Q i = oldR M A (i + r) := by
  funext x y
  unfold newW oldR
  rw [nc_A (by omega : i < m) rfl, nc_A (by omega : i + 1 < m) (show i + r + 1 = i + 1 + r by omega),
    nc_A hi (show i + r + 2 = i + 2 + r by omega)]

theorem newW_a (hm : 2 ≤ m) (x y : Bool) : newW M m r A P Q (m - 2) x y ↔
    M.IsBase {A (m - 2 + r) (!x), A (m - 1 + r) false, A (m - 1 + r) true, P y} := by
  unfold newW
  rw [nc_A (by omega : m - 2 < m) rfl,
    nc_A (by omega : m - 2 + 1 < m) (show m - 1 + r = m - 2 + 1 + r by omega),
    show m - 2 + 2 = m by omega, nc_P]

theorem newW_b (hm : 1 ≤ m) (x y : Bool) : newW M m r A P Q (m - 1) x y ↔
    M.IsBase {A (m - 1 + r) (!x), P false, P true, Q y} := by
  unfold newW
  rw [nc_A (by omega : m - 1 < m) rfl, show m - 1 + 1 = m by omega, nc_P,
    show m - 1 + 2 = m + 1 by omega, nc_Q]

theorem newW_c (hm : 0 < m) (x y : Bool) : newW M m r A P Q m x y ↔
    M.IsBase {P (!x), Q false, Q true, A r y} := by
  unfold newW
  rw [nc_P, nc_Q, nc_A0 hm]

theorem newW_d (hm : 1 < m) (x y : Bool) : newW M m r A P Q (m + 1) x y ↔
    M.IsBase {Q (!x), A r false, A r true, A (1 + r) y} := by
  unfold newW
  rw [nc_Q, show m + 1 + 1 = m + 2 by omega, nc_A0 (by omega), show m + 1 + 2 = m + 3 by omega,
    nc_A1 hm]

end NewChain

/-- A split `(P, Q)` of `S`, inserted after the old pair `m - 1 + r`, valid. -/
structure Ins (M : Matroid α) (m r : ℕ) (A : ℕ → Bool → α) (S : Set α) (P Q : Bool → α) :
    Prop where
  hSPQ : S = {P false, P true, Q false, Q true}
  V1 : M.IsBase {A (m - 1 + r) false, A (m - 1 + r) true, P false, P true}
  V2 : M.IsBase {Q false, Q true, A r false, A r true}

namespace Ins

variable {m r : ℕ} {A : ℕ → Bool → α} {S : Set α} {P Q : Bool → α}

/-- Consecutive pairs of the new chain form bases. -/
theorem even_lt (hm : 2 ≤ m) (hA : OldChain M m A S) (hS : M.IsBase S)
    (hI : Ins M m r A S P Q) {i : ℕ} (hi : i < m + 2) :
    M.IsBase {newChain m r A P Q i false, newChain m r A P Q i true,
      newChain m r A P Q (i + 1) false, newChain m r A P Q (i + 1) true} := by
  rcases (show i + 1 < m ∨ i = m - 1 ∨ i = m ∨ i = m + 1 by omega) with h | h | h | h
  · rw [nc_A (by omega : i < m) rfl, nc_A h (show i + r + 1 = i + 1 + r by omega)]
    exact hA.even (i + r)
  · rw [h, nc_A (by omega : m - 1 < m) rfl, show m - 1 + 1 = m by omega, nc_P]
    exact hI.V1
  · rw [h, nc_P, nc_Q]
    rw [hI.hSPQ] at hS
    exact hS
  · rw [h, nc_Q, show m + 1 + 1 = m + 2 by omega, nc_A0 (by omega)]
    exact hI.V2

theorem even (hm : 2 ≤ m) (hA : OldChain M m A S) (hS : M.IsBase S) (hI : Ins M m r A S P Q)
    (i : ℕ) :
    M.IsBase {newChain m r A P Q i false, newChain m r A P Q i true,
      newChain m r A P Q (i + 1) false, newChain m r A P Q (i + 1) true} := by
  have h := hI.even_lt hm hA hS (Nat.mod_lt i (by omega : 0 < m + 2))
  rwa [nc_mod, nc_succ_mod] at h

/-- Rows of the new relations are nonempty. -/
theorem row (hRank : M.eRank = 4) (hm : 2 ≤ m) (hA : OldChain M m A S) (hS : M.IsBase S)
    (hI : Ins M m r A S P Q) (i : ℕ) (x : Bool) :
    ∃ y, newW M m r A P Q i x y := by
  have h1 := hI.even hm hA hS i
  have h2 := hI.even hm hA hS (i + 1)
  rw [show i + 1 + 1 = i + 2 by omega] at h2
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank h1
  have key : newW M m r A P Q i x false ∨ newW M m r A P Q i x true := by
    unfold newW
    cases x <;> simp only [Bool.not_false, Bool.not_true] <;>
      exact exists_isBase_augment hRank (h1.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac)
        (by ne_tac) h2
  rcases key with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

end Ins

/-! ### The local lemma at the insertion point -/

theorem oldR_m2 {m r : ℕ} {A : ℕ → Bool → α} {S : Set α} (hA : OldChain M m A S) (hm : 2 ≤ m)
    (x y : Bool) : oldR M A (m - 2 + r) x y ↔
      M.IsBase {A (m - 2 + r) (!x), A (m - 1 + r) false, A (m - 1 + r) true, A r y} := by
  unfold oldR
  rw [show m - 2 + r + 1 = m - 1 + r by omega, show m - 2 + r + 2 = r + m by omega, hA.per]

theorem oldR_m1 {m r : ℕ} {A : ℕ → Bool → α} {S : Set α} (hA : OldChain M m A S) (hm : 1 ≤ m)
    (x y : Bool) : oldR M A (m - 1 + r) x y ↔
      M.IsBase {A (m - 1 + r) (!x), A r false, A r true, A (1 + r) y} := by
  unfold oldR
  rw [show m - 1 + r + 1 = r + m by omega, show m - 1 + r + 2 = 1 + r + m by omega, hA.per,
    hA.per]

/-- **The local lemmas at the insertion point.** A valid split; if `R_{m-2+r}` is tight, the
P-side constraint (`Wa`, `Wc`) is `Good`; if `R_{m-1+r}` is tight, the Q-side constraint (`Wb`,
`Wd`) is `Good`. -/
theorem local_at (hRank : M.eRank = 4) {m : ℕ} (hm : 4 ≤ m) {A : ℕ → Bool → α} {S : Set α}
    (hA : OldChain M m A S) (hS : M.IsBase S) (r : ℕ) :
    ∃ P Q, Ins M m r A S P Q ∧
      (¬ Slack (oldR M A (m - 2 + r)) → Good (fun e1 e2 => ∃ oP,
        newW M m r A P Q (m - 2) e1 oP ∧ newW M m r A P Q m oP e2)) ∧
      (¬ Slack (oldR M A (m - 1 + r)) → Good (fun e1 e2 => ∃ oQ,
        newW M m r A P Q (m - 1) e2 oQ ∧ newW M m r A P Q (m + 1) oQ e1)) := by
  have hAB : M.IsBase {A (m - 1 + r) false, A (m - 1 + r) true, A r false, A r true} := by
    have h := hA.even (m - 1 + r)
    rwa [show m - 1 + r + 1 = r + m by omega, hA.per] at h
  have hXA : M.IsBase {A (m - 2 + r) false, A (m - 2 + r) true, A (m - 1 + r) false,
      A (m - 1 + r) true} := by
    have h := hA.even (m - 2 + r)
    rwa [show m - 2 + r + 1 = m - 1 + r by omega] at h
  have hBY : M.IsBase {A r false, A r true, A (1 + r) false, A (1 + r) true} := by
    have h := hA.even r
    rwa [show r + 1 = 1 + r by omega] at h
  have hdisj : Disjoint S {A (m - 1 + r) false, A (m - 1 + r) true, A r false, A r true} := by
    rw [Set.disjoint_left]
    intro x hxS hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact hA.notS _ _ hxS
  obtain ⟨P, Q, hSPQ, hV1, hV2, hGP, hGQ⟩ := local_xp hRank hS (A (m - 2 + r)) (A (m - 1 + r))
    (A r) (A (1 + r)) hAB hXA hBY hdisj
  refine ⟨P, Q, ⟨hSPQ, hV1, hV2⟩, fun ht => ?_, fun ht => ?_⟩
  · have htt := hA.tt_of_tight hRank (m - 2 + r) ht
    have t1 : ¬ M.IsBase {A (m - 2 + r) false, A (m - 1 + r) false, A (m - 1 + r) true,
        A r false} := by
      have h := htt.2.2
      rw [oldR_m2 hA (by omega)] at h
      simp only [Bool.not_true] at h
      exact h
    have t2 : ¬ M.IsBase {A (m - 2 + r) true, A (m - 1 + r) false, A (m - 1 + r) true,
        A r true} := by
      have h := htt.2.1
      rw [oldR_m2 hA (by omega)] at h
      simp only [Bool.not_false] at h
      exact h
    refine Good.mono ?_ (hGP ⟨t1, t2⟩)
    rintro e1 e2 ⟨oP, h1, h2⟩
    exact ⟨oP, (newW_a (by omega) e1 oP).2 h1, (newW_c (by omega) oP e2).2 h2⟩
  · have htt := hA.tt_of_tight hRank (m - 1 + r) ht
    have t1 : ¬ M.IsBase {A (m - 1 + r) false, A r false, A r true, A (1 + r) false} := by
      have h := htt.2.2
      rw [oldR_m1 hA (by omega)] at h
      simp only [Bool.not_true] at h
      exact h
    have t2 : ¬ M.IsBase {A (m - 1 + r) true, A r false, A r true, A (1 + r) true} := by
      have h := htt.2.1
      rw [oldR_m1 hA (by omega)] at h
      simp only [Bool.not_false] at h
      exact h
    refine Good.mono ?_ (hGQ ⟨t1, t2⟩)
    rintro e1 e2 ⟨oQ, h1, h2⟩
    exact ⟨oQ, (newW_b (by omega) e2 oQ).2 h1, (newW_d (by omega) oQ e1).2 h2⟩

/-! ### Orientations -/

/-- Positions `i` and `i + 2` of a class of an even cycle. -/
theorem class_step {n : ℕ} (hn : n % 2 = 0) {c : ℕ} (hc : c < 2) {i : ℕ} (hi : i < n)
    (hic : i % 2 = c) :
    i / 2 < n / 2 ∧ ((i + 2) % n) % 2 = c ∧ ((i + 2) % n) / 2 = (i / 2 + 1) % (n / 2) ∧
      c + 2 * (i / 2) = i := by
  rcases Nat.lt_or_ge (i + 2) n with h | h
  · have h1 : i / 2 + 1 < n / 2 := by omega
    rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt h1]
    omega
  · have e : i + 2 = n + c := by omega
    have h1 : i / 2 + 1 = n / 2 := by omega
    rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : c < n), h1, Nat.mod_self]
    omega

section Orient

variable {m r : ℕ} {A : ℕ → Bool → α} {S : Set α} {P Q : Bool → α}

/-- `m` odd, a slack relation at `m - 3`: one cycle, oriented by the cycle lemma. -/
theorem orient_O1 (hRank : M.eRank = 4) (hm : 4 ≤ m) (hmo : m % 2 = 1) (hA : OldChain M m A S)
    (hS : M.IsBase S) (hI : Ins M m r A S P Q) (hsl : Slack (oldR M A (m - 3 + r))) :
    ∃ o : ℕ → Bool, ∀ i < m + 2, newW M m r A P Q i (o i) (o ((i + 2) % (m + 2))) := by
  refine orient_odd (by omega) (by omega) (newW M m r A P Q)
    (fun i _ x => hI.row hRank (by omega) hA hS i x) (k := m - 3) (by omega) ?_
  rw [newW_old (by omega)]
  exact hsl

/-- `m` even, slack relations at `i₀` (even, `≤ m - 4`) and `m - 3`: two cycles, both oriented by
the cycle lemma. -/
theorem orient_O2 (hRank : M.eRank = 4) (hm : 4 ≤ m) (hme : m % 2 = 0) (hA : OldChain M m A S)
    (hS : M.IsBase S) (hI : Ins M m r A S P Q) (hslQ : Slack (oldR M A (m - 3 + r))) {i0 : ℕ}
    (hi0 : i0 + 4 ≤ m) (hi0e : i0 % 2 = 0) (hslP : Slack (oldR M A (i0 + r))) :
    ∃ o : ℕ → Bool, ∀ i < m + 2, newW M m r A P Q i (o i) (o ((i + 2) % (m + 2))) := by
  obtain ⟨xP, hxP⟩ := cycle_sat (L := (m + 2) / 2) (fun t => newW M m r A P Q (0 + 2 * t))
    (fun t _ x => hI.row hRank (by omega) hA hS _ x) (k := i0 / 2) (by omega)
    (by
      show Slack (newW M m r A P Q (0 + 2 * (i0 / 2)))
      rw [show 0 + 2 * (i0 / 2) = i0 by omega, newW_old (by omega)]
      exact hslP)
  obtain ⟨xQ, hxQ⟩ := cycle_sat (L := (m + 2) / 2) (fun t => newW M m r A P Q (1 + 2 * t))
    (fun t _ x => hI.row hRank (by omega) hA hS _ x) (k := (m - 3) / 2) (by omega)
    (by
      show Slack (newW M m r A P Q (1 + 2 * ((m - 3) / 2)))
      rw [show 1 + 2 * ((m - 3) / 2) = m - 3 by omega, newW_old (by omega)]
      exact hslQ)
  refine ⟨fun i => if i % 2 = 0 then xP (i / 2) else xQ (i / 2), fun i hi => ?_⟩
  show newW M m r A P Q i (if i % 2 = 0 then xP (i / 2) else xQ (i / 2))
    (if (i + 2) % (m + 2) % 2 = 0 then xP ((i + 2) % (m + 2) / 2) else xQ ((i + 2) % (m + 2) / 2))
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · obtain ⟨h1, h2, h3, h4⟩ := class_step (n := m + 2) (by omega) (c := 0) (by omega) hi he
    have h := (hxP (i / 2) h1 : newW M m r A P Q (0 + 2 * (i / 2)) (xP (i / 2))
      (xP ((i / 2 + 1) % ((m + 2) / 2))))
    rw [h4] at h
    rw [if_pos he, if_pos h2, h3]
    exact h
  · obtain ⟨h1, h2, h3, h4⟩ := class_step (n := m + 2) (by omega) (c := 1) (by omega) hi ho
    have h := (hxQ (i / 2) h1 : newW M m r A P Q (1 + 2 * (i / 2)) (xQ (i / 2))
      (xQ ((i / 2 + 1) % ((m + 2) / 2))))
    rw [h4] at h
    rw [if_neg (by omega), if_neg (by omega), h3]
    exact h

/-- The orientation of the tight cycles: every old pair of a class is flipped by the same bit,
`e₁` for the class of `m`, `e₂` for the other; `P` and `Q` are oriented by `o_P` and `o_Q`. -/
def tightO (m : ℕ) (e1 e2 oP oQ : Bool) (i : ℕ) : Bool :=
  if i < m then (if i % 2 = m % 2 then e1 else e2) else if i = m then oP else oQ

/-- All relations tight: both cycles (or the one cycle) are oriented by `tightO`. -/
theorem orient_O3 (hm : 4 ≤ m) (hA : OldChain M m A S) (e1 e2 oP oQ : Bool)
    (hold : ∀ i, i + 2 < m → oldR M A (i + r) true true)
    (hWa : newW M m r A P Q (m - 2) e1 oP) (hWb : newW M m r A P Q (m - 1) e2 oQ)
    (hWc : newW M m r A P Q m oP (if 0 % 2 = m % 2 then e1 else e2))
    (hWd : newW M m r A P Q (m + 1) oQ (if 1 % 2 = m % 2 then e1 else e2)) :
    ∃ o : ℕ → Bool, ∀ i < m + 2, newW M m r A P Q i (o i) (o ((i + 2) % (m + 2))) := by
  refine ⟨tightO m e1 e2 oP oQ, fun i hi => ?_⟩
  rcases (show i + 2 < m ∨ i = m - 2 ∨ i = m - 1 ∨ i = m ∨ i = m + 1 by omega)
    with h | h | h | h | h
  · rw [Nat.mod_eq_of_lt (by omega : i + 2 < m + 2), newW_old h]
    have e : tightO m e1 e2 oP oQ (i + 2) = tightO m e1 e2 oP oQ i := by
      unfold tightO
      rw [if_pos h, if_pos (by omega : i < m), show (i + 2) % 2 = i % 2 by omega]
    rw [e]
    generalize tightO m e1 e2 oP oQ i = b
    cases b
    · exact hA.odd (i + r)
    · exact hold i h
  · rw [h, show m - 2 + 2 = m by omega, Nat.mod_eq_of_lt (by omega : m < m + 2)]
    have e1' : tightO m e1 e2 oP oQ (m - 2) = e1 := by
      unfold tightO
      rw [if_pos (by omega : m - 2 < m), if_pos (by omega : (m - 2) % 2 = m % 2)]
    have e2' : tightO m e1 e2 oP oQ m = oP := by
      unfold tightO
      rw [if_neg (lt_irrefl m), if_pos rfl]
    rw [e1', e2']
    exact hWa
  · rw [h, show m - 1 + 2 = m + 1 by omega, Nat.mod_eq_of_lt (by omega : m + 1 < m + 2)]
    have e1' : tightO m e1 e2 oP oQ (m - 1) = e2 := by
      unfold tightO
      rw [if_pos (by omega : m - 1 < m), if_neg (by omega : ¬ (m - 1) % 2 = m % 2)]
    have e2' : tightO m e1 e2 oP oQ (m + 1) = oQ := by
      unfold tightO
      rw [if_neg (by omega : ¬ m + 1 < m), if_neg (by omega : ¬ m + 1 = m)]
    rw [e1', e2']
    exact hWb
  · rw [h, Nat.mod_self]
    have e1' : tightO m e1 e2 oP oQ m = oP := by
      unfold tightO
      rw [if_neg (lt_irrefl m), if_pos rfl]
    have e2' : tightO m e1 e2 oP oQ 0 = if 0 % 2 = m % 2 then e1 else e2 := by
      unfold tightO
      rw [if_pos (by omega : 0 < m)]
    rw [e1', e2']
    exact hWc
  · rw [h, show m + 1 + 2 = (m + 2) + 1 by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : 1 < m + 2)]
    have e1' : tightO m e1 e2 oP oQ (m + 1) = oQ := by
      unfold tightO
      rw [if_neg (by omega : ¬ m + 1 < m), if_neg (by omega : ¬ m + 1 = m)]
    have e2' : tightO m e1 e2 oP oQ 1 = if 1 % 2 = m % 2 then e1 else e2 := by
      unfold tightO
      rw [if_pos (by omega : 1 < m)]
    rw [e1', e2']
    exact hWd

/-- The mixed orientation (`m` even): the cycle through `P` (even positions) is tight and
flipped by `e₁`, the cycle through `Q` (odd positions) is oriented by `xQ`. -/
def mixO (m : ℕ) (e1 oP : Bool) (xQ : ℕ → Bool) (i : ℕ) : Bool :=
  if i % 2 = 0 then (if i < m then e1 else oP) else xQ (i / 2)

/-- `m` even, the cycle through `P` tight, a slack relation at `m - 3`. -/
theorem orient_O4 (hRank : M.eRank = 4) (hm : 4 ≤ m) (hme : m % 2 = 0) (hA : OldChain M m A S)
    (hS : M.IsBase S) (hI : Ins M m r A S P Q) (e1 oP : Bool)
    (holdP : ∀ i, i + 2 < m → i % 2 = 0 → oldR M A (i + r) true true)
    (hWa : newW M m r A P Q (m - 2) e1 oP) (hWc : newW M m r A P Q m oP e1)
    (hslQ : Slack (oldR M A (m - 3 + r))) :
    ∃ o : ℕ → Bool, ∀ i < m + 2, newW M m r A P Q i (o i) (o ((i + 2) % (m + 2))) := by
  obtain ⟨xQ, hxQ⟩ := cycle_sat (L := (m + 2) / 2) (fun t => newW M m r A P Q (1 + 2 * t))
    (fun t _ x => hI.row hRank (by omega) hA hS _ x) (k := (m - 3) / 2) (by omega)
    (by
      show Slack (newW M m r A P Q (1 + 2 * ((m - 3) / 2)))
      rw [show 1 + 2 * ((m - 3) / 2) = m - 3 by omega, newW_old (by omega)]
      exact hslQ)
  refine ⟨mixO m e1 oP xQ, fun i hi => ?_⟩
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · rcases (show i + 2 < m ∨ i = m - 2 ∨ i = m by omega) with h | h | h
    · rw [Nat.mod_eq_of_lt (by omega : i + 2 < m + 2), newW_old h]
      have ea : mixO m e1 oP xQ i = e1 := by
        unfold mixO
        rw [if_pos he, if_pos (by omega : i < m)]
      have eb : mixO m e1 oP xQ (i + 2) = e1 := by
        unfold mixO
        rw [if_pos (by omega : (i + 2) % 2 = 0), if_pos h]
      rw [ea, eb]
      cases e1
      · exact hA.odd (i + r)
      · exact holdP i h he
    · rw [h, show m - 2 + 2 = m by omega, Nat.mod_eq_of_lt (by omega : m < m + 2)]
      have ea : mixO m e1 oP xQ (m - 2) = e1 := by
        unfold mixO
        rw [if_pos (by omega : (m - 2) % 2 = 0), if_pos (by omega : m - 2 < m)]
      have eb : mixO m e1 oP xQ m = oP := by
        unfold mixO
        rw [if_pos hme, if_neg (lt_irrefl m)]
      rw [ea, eb]
      exact hWa
    · rw [h, Nat.mod_self]
      have ea : mixO m e1 oP xQ m = oP := by
        unfold mixO
        rw [if_pos hme, if_neg (lt_irrefl m)]
      have eb : mixO m e1 oP xQ 0 = e1 := by
        unfold mixO
        rw [if_pos (by omega : 0 % 2 = 0), if_pos (by omega : 0 < m)]
      rw [ea, eb]
      exact hWc
  · obtain ⟨h1, h2, h3, h4⟩ := class_step (n := m + 2) (by omega) (c := 1) (by omega) hi ho
    have h := (hxQ (i / 2) h1 : newW M m r A P Q (1 + 2 * (i / 2)) (xQ (i / 2))
      (xQ ((i / 2 + 1) % ((m + 2) / 2))))
    rw [h4] at h
    have ea : mixO m e1 oP xQ i = xQ (i / 2) := by
      unfold mixO
      rw [if_neg (by omega)]
    have eb : mixO m e1 oP xQ ((i + 2) % (m + 2)) = xQ ((i / 2 + 1) % ((m + 2) / 2)) := by
      unfold mixO
      rw [if_neg (by omega), h3]
    rw [ea, eb]
    exact h

end Orient

/-! ### The choice of the rotation -/

theorem choice_even {m : ℕ} (hm : 4 ≤ m) (hme : m % 2 = 0) (R : ℕ → Bool → Bool → Prop)
    (hper : ∀ k, R (k + m) = R k) {k : ℕ} (hk : Slack (R k)) :
    ∃ r, Slack (R (m - 3 + r)) ∧
      ((∃ i, i + 4 ≤ m ∧ i % 2 = 0 ∧ Slack (R (i + r))) ∨
        (∀ i, i % 2 = 0 → ¬ Slack (R (i + r)))) := by
  have hq : ∀ x q, R (x + m * q) = R x := by
    intro x q
    induction q with
    | zero => simp
    | succ q ih => rw [show x + m * (q + 1) = (x + m * q) + m by ring, hper, ih]
  have hmod : ∀ x, R x = R (x % m) := by
    intro x
    conv_lhs => rw [← Nat.mod_add_div x m]
    exact hq _ _
  have hk3 : Slack (R (m - 3 + (k + 3))) := by
    rw [show m - 3 + (k + 3) = k + m by omega, hper]
    exact hk
  by_cases h : ∀ i, i % 2 = 0 → ¬ Slack (R (i + (k + 3)))
  · exact ⟨k + 3, hk3, Or.inr h⟩
  · push_neg at h
    obtain ⟨i, hi, hs⟩ := h
    have hi' : i % m % 2 = 0 := by rw [Nat.mod_mod_of_dvd i (by omega : 2 ∣ m)]; exact hi
    have hs' : Slack (R (i % m + (k + 3))) := by
      rw [hmod (i % m + (k + 3)), Nat.mod_add_mod, ← hmod]
      exact hs
    have hlt : i % m < m := Nat.mod_lt i (by omega)
    by_cases h4 : i % m + 4 ≤ m
    · exact ⟨k + 3, hk3, Or.inl ⟨i % m, h4, hi', hs'⟩⟩
    · have h2 : i % m = m - 2 := by omega
      refine ⟨k + 4, ?_, Or.inl ⟨m - 4, by omega, by omega, ?_⟩⟩
      · rw [show m - 3 + (k + 4) = m - 2 + (k + 3) by omega, ← h2]
        exact hs'
      · rw [show m - 4 + (k + 4) = k + m by omega, hper]
        exact hk

/-! ### The new chain exists -/

theorem exists_newChain (hRank : M.eRank = 4) {m : ℕ} (hm : 4 ≤ m) {A : ℕ → Bool → α}
    {S : Set α} (hA : OldChain M m A S) (hS : M.IsBase S) :
    ∃ r P Q, Ins M m r A S P Q ∧
      ∃ o : ℕ → Bool, ∀ i < m + 2, newW M m r A P Q i (o i) (o ((i + 2) % (m + 2))) := by
  by_cases hsl : ∃ k, Slack (oldR M A k)
  · obtain ⟨k, hk⟩ := hsl
    rcases Nat.mod_two_eq_zero_or_one m with hme | hmo
    · obtain ⟨r, hr1, hr2⟩ := choice_even hm hme (oldR M A) hA.perR hk
      obtain ⟨P, Q, hI, hGP, -⟩ := local_at hRank hm hA hS r
      refine ⟨r, P, Q, hI, ?_⟩
      rcases hr2 with ⟨i0, hi0, hi0e, hs0⟩ | htP
      · exact orient_O2 hRank hm hme hA hS hI hr1 hi0 hi0e hs0
      · obtain ⟨e1, oP, hWa, hWc⟩ := (hGP (htP (m - 2) (by omega))).diag
        exact orient_O4 hRank hm hme hA hS hI e1 oP
          (fun i _ hie => (hA.tt_of_tight hRank (i + r) (htP i hie)).1) hWa hWc hr1
    · obtain ⟨P, Q, hI, -, -⟩ := local_at hRank hm hA hS (k + 3)
      refine ⟨k + 3, P, Q, hI, orient_O1 hRank hm hmo hA hS hI ?_⟩
      rw [show m - 3 + (k + 3) = k + m by omega, hA.perR]
      exact hk
  · push_neg at hsl
    obtain ⟨P, Q, hI, hGP, hGQ⟩ := local_at hRank hm hA hS 0
    have hold : ∀ i, i + 2 < m → oldR M A (i + 0) true true := fun i _ =>
      (hA.tt_of_tight hRank _ (hsl _)).1
    refine ⟨0, P, Q, hI, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one m with hme | hmo
    · obtain ⟨e1, oP, hWa, hWc⟩ := (hGP (hsl _)).diag
      obtain ⟨e2, oQ, hWb, hWd⟩ := (hGQ (hsl _)).diag
      exact orient_O3 hm hA e1 e2 oP oQ hold hWa hWb
        (by rw [if_pos (by omega)]; exact hWc) (by rw [if_neg (by omega)]; exact hWd)
    · obtain ⟨e1, e2, ⟨oP, hWa, hWc⟩, ⟨oQ, hWb, hWd⟩⟩ := Good.common (hGP (hsl _)) (hGQ (hsl _))
      exact orient_O3 hm hA e1 e2 oP oQ hold hWa hWb
        (by rw [if_neg (by omega)]; exact hWc) (by rw [if_pos (by omega)]; exact hWd)

/-! ### From a cyclic basis ordering of `M \ S` -/

section Old

variable {E : Set α} {N : ℕ}

/-- The old sequence, read periodically. -/
def oldSeq (hN : 0 < N) (σ : Fin N ≃ E) (k : ℕ) : α := σ ⟨k % N, Nat.mod_lt _ hN⟩

/-- Old pair `i`: `(e_{2i}, e_{2i+1})`. -/
def oldPair (hN : 0 < N) (σ : Fin N ≃ E) (i : ℕ) : Bool → α
  | false => oldSeq hN σ (2 * i)
  | true => oldSeq hN σ (2 * i + 1)

theorem oldSeq_mem (hN : 0 < N) (σ : Fin N ≃ E) (k : ℕ) : oldSeq hN σ k ∈ E := (σ _).2

theorem oldSeq_add (hN : 0 < N) (σ : Fin N ≃ E) (k : ℕ) : oldSeq hN σ (k + N) = oldSeq hN σ k := by
  unfold oldSeq
  rw [show (⟨(k + N) % N, Nat.mod_lt _ hN⟩ : Fin N) = ⟨k % N, Nat.mod_lt _ hN⟩ from
    Fin.ext (Nat.add_mod_right k N)]

theorem oldSeq_win (hN : 0 < N) (σ : Fin N ≃ E) (hσ : CyclicBasisOrder M 4 hN σ) (k : ℕ) :
    M.IsBase {oldSeq hN σ k, oldSeq hN σ (k + 1), oldSeq hN σ (k + 2), oldSeq hN σ (k + 3)} := by
  have h := hσ ⟨k % N, Nat.mod_lt _ hN⟩
  have hv : ∀ j : ℕ,
      (σ (cyclicIndex N hN ⟨k % N, Nat.mod_lt _ hN⟩ j) : α) = oldSeq hN σ (k + j) := by
    intro j
    unfold oldSeq
    rw [show cyclicIndex N hN ⟨k % N, Nat.mod_lt _ hN⟩ j = ⟨(k + j) % N, Nat.mod_lt _ hN⟩ from
      Fin.ext (by simp [cyclicIndex_val, Nat.mod_add_mod])]
  have e : cyclicWindow 4 hN σ ⟨k % N, Nat.mod_lt _ hN⟩ =
      {oldSeq hN σ k, oldSeq hN σ (k + 1), oldSeq hN σ (k + 2), oldSeq hN σ (k + 3)} := by
    ext x
    simp only [cyclicWindow, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, hv]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨3, by simp⟩
  rw [e] at h
  exact h

theorem oldSeq_surj (hN : 0 < N) (σ : Fin N ≃ E) {x : α} (hx : x ∈ E) (a : ℕ) :
    ∃ t < N, oldSeq hN σ (a + t) = x := by
  let f : Fin N → Fin N := fun t => ⟨(a + t) % N, Nat.mod_lt _ hN⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have h1 : (a + p) % N = (a + q) % N := congrArg Fin.val hpq
    exact Fin.ext ((Nat.ModEq.add_left_cancel' a h1).eq_of_lt_of_lt p.2 q.2)
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 hf) (σ.symm ⟨x, hx⟩)
  refine ⟨t, t.2, ?_⟩
  have h1 : (⟨(a + t) % N, Nat.mod_lt _ hN⟩ : Fin N) = σ.symm ⟨x, hx⟩ := ht
  unfold oldSeq
  rw [h1, Equiv.apply_symm_apply]

end Old

theorem oldChain_of_cbo {S : Set α} {m : ℕ} (hN : 0 < 2 * m) (σ : Fin (2 * m) ≃ (M.E \ S : Set α))
    (hσ : CyclicBasisOrder M 4 hN σ) : OldChain M m (oldPair hN σ) S where
  per k := by
    funext b
    cases b
    · show oldSeq hN σ (2 * (k + m)) = oldSeq hN σ (2 * k)
      rw [show 2 * (k + m) = 2 * k + 2 * m by ring, oldSeq_add]
    · show oldSeq hN σ (2 * (k + m) + 1) = oldSeq hN σ (2 * k + 1)
      rw [show 2 * (k + m) + 1 = 2 * k + 1 + 2 * m by ring, oldSeq_add]
  even k := by
    have h := oldSeq_win hN σ hσ (2 * k)
    show M.IsBase {oldSeq hN σ (2 * k), oldSeq hN σ (2 * k + 1), oldSeq hN σ (2 * (k + 1)),
      oldSeq hN σ (2 * (k + 1) + 1)}
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 2 + 1 = 2 * k + 3 by ring]
    exact h
  odd k := by
    have h := oldSeq_win hN σ hσ (2 * k + 1)
    show M.IsBase {oldSeq hN σ (2 * k + 1), oldSeq hN σ (2 * (k + 1)),
      oldSeq hN σ (2 * (k + 1) + 1), oldSeq hN σ (2 * (k + 2))}
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      show 2 * (k + 2) = 2 * k + 1 + 3 by ring]
    exact h
  notS k b := by
    cases b
    · exact (oldSeq_mem hN σ _).2
    · exact (oldSeq_mem hN σ _).2

/-- **The rank-4 extension theorem for even `N ≥ 8`**, by pair-chain insertion. -/
theorem rank4Extension_of_even {N : ℕ} (h8 : 8 ≤ N) (heven : Even N) : Rank4Extension α N := by
  intro M S hN hE hRank hS hσ
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨m, rfl⟩ : ∃ m, N = 2 * m := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k, by omega⟩
  have hm : 4 ≤ m := by omega
  have hA := oldChain_of_cbo hN σ hσ
  obtain ⟨r, P, Q, hI, o, ho⟩ := exists_newChain hRank hm hA hS
  have hn : 0 < m + 2 := by omega
  have hcard : M.E.ncard = 2 * (m + 2) := by
    have h1 : (M.E \ S).ncard = 2 * m := by
      rw [← Nat.card_coe_set_eq, Nat.card_congr σ.symm]
      simp
    have h2 : S.ncard = 4 := KotlarZiv.ncard_eq_four hS hRank
    have h3 := Set.ncard_sdiff_add_ncard_of_subset hS.subset_ground hE
    omega
  have hmem : ∀ i b, newChain m r (oldPair hN σ) P Q i b ∈ M.E := by
    intro i b
    unfold newChain newPair
    split_ifs
    · exact hA.mem _ _
    · have hb : P b ∈ S := by rw [hI.hSPQ]; cases b <;> simp
      exact hS.subset_ground hb
    · have hb : Q b ∈ S := by rw [hI.hSPQ]; cases b <;> simp
      exact hS.subset_ground hb
  have hsurj : ∀ x ∈ M.E, ∃ i < m + 2, ∃ b, newChain m r (oldPair hN σ) P Q i b = x := by
    intro x hx
    by_cases hxS : x ∈ S
    · rw [hI.hSPQ] at hxS
      simp only [mem_insert_iff, mem_singleton_iff] at hxS
      rcases hxS with rfl | rfl | rfl | rfl
      · exact ⟨m, by omega, false, by rw [nc_P]⟩
      · exact ⟨m, by omega, true, by rw [nc_P]⟩
      · exact ⟨m + 1, by omega, false, by rw [nc_Q]⟩
      · exact ⟨m + 1, by omega, true, by rw [nc_Q]⟩
    · obtain ⟨t, ht, htx⟩ := oldSeq_surj hN σ ⟨hx, hxS⟩ (2 * r)
      rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
      · refine ⟨t / 2, by omega, false, ?_⟩
        rw [nc_A (by omega : t / 2 < m) rfl]
        show oldSeq hN σ (2 * (t / 2 + r)) = x
        rw [show 2 * (t / 2 + r) = 2 * r + t by omega]
        exact htx
      · refine ⟨t / 2, by omega, true, ?_⟩
        rw [nc_A (by omega : t / 2 < m) rfl]
        show oldSeq hN σ (2 * (t / 2 + r) + 1) = x
        rw [show 2 * (t / 2 + r) + 1 = 2 * r + t by omega]
        exact htx
  obtain ⟨τ, hτ⟩ := cbo_of_chain hn (newChain m r (oldPair hN σ) P Q) (fun i => o (i % (m + 2)))
    nc_per (fun i => by show o ((i + (m + 2)) % (m + 2)) = o (i % (m + 2)); rw [Nat.add_mod_right])
    hmem hsurj hcard (fun i hi => hI.even_lt (by omega) hA hS hi)
    (fun i hi => by
      show M.IsBase {newChain m r (oldPair hN σ) P Q i (!o (i % (m + 2))),
        newChain m r (oldPair hN σ) P Q (i + 1) false, newChain m r (oldPair hN σ) P Q (i + 1) true,
        newChain m r (oldPair hN σ) P Q (i + 2) (o ((i + 2) % (m + 2)))}
      rw [Nat.mod_eq_of_lt hi]
      exact ho i hi)
  exact exists_cyclicBasisOrder_congr M (by ring) rfl ⟨τ, hτ⟩

#print axioms rank4Extension_of_even

end HigherRankKUM.XP
