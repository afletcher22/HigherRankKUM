import Probe.XP.Basic

/-!
# Pair-chain insertion (XP): the 8-element Main Lemma

Part B of `docs/research-ledger/XP_LOCAL_LEMMAS_ODD_EVEN.md`. Let `M` have rank 4, and let
`A₀ = {a₀, a₁}`, `A₁ = {b₀, b₁}` and `S` be disjoint, with `A₀ ∪ A₁` and `S` bases.

An ordered split `(P, Q) = ({p₀, p₁}, {q₀, q₁})` of `S` is **valid** if `A₀ ∪ P` and `Q ∪ A₁` are
bases. It is **P-crossed** if `P` can be labelled `(u, v)` with

  `u ∈ cl(A₀ + b₀)`, `v ∈ cl(A₀ + b₁)`, `b₁ ∈ cl(Q + u)` and `b₀ ∈ cl(Q + v)`,

and **Q-crossed** if it is P-crossed in the mirror configuration (`A₀ ↔ A₁`, `P ↔ Q`).

**Main Lemma** (`main_lemma`): some valid split is neither P-crossed nor Q-crossed.

* Greene–Magnanti (`exists_valid_split`, from the Kotlar–Ziv serial exchange of pairs) gives a
  valid split.
* If it is P-crossed, label it `({u, v}, {w, z})` (`Std`). One of the one-swap splits
  `X_w = ({u, w}, {v, z})` and `X_z = ({u, z}, {v, w})` is valid and not P-crossed (Lemma F1,
  claims 9.0–9.7), and neither is Q-crossed (Lemma F2).
* If it is Q-crossed, apply the previous case to the mirror.

Everything uses only closure, exchange and "two flats `cl(X + g)` and `cl(X + h)` with
`h ∉ cl(X + g)` meet in `cl X`" (`mem_closure_of_mem_two`).
-/

namespace HigherRankKUM.XP

open Set

variable {α : Type*} {M : Matroid α}

/-! ### Helpers -/

/-- `a ≠ b` from a hypothesis `a ≠ b` or `b ≠ a`. -/
macro "ne_tac" : tactic => `(tactic| first | assumption | exact Ne.symm ‹_›)

/-- `e ∉ {x, y, …}` from hypotheses `e ≠ x`, … (in either orientation). -/
macro "notin_tac" : tactic =>
  `(tactic| (simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or];
    repeat' apply And.intro; all_goals ne_tac))

theorem isBase_perm {X Y : Set α} (h : M.IsBase X) (e : X = Y) : M.IsBase Y := e ▸ h

theorem mem_closure_perm {X Y : Set α} {x : α} (h : x ∈ M.closure X) (e : X = Y) :
    x ∈ M.closure Y := e ▸ h

theorem notMem_closure_of_indep_insert {X : Set α} {e : α} (h : M.Indep (insert e X))
    (he : e ∉ X) : e ∉ M.closure X :=
  ((h.subset (subset_insert e X)).insert_indep_iff_of_notMem he).1 h |>.2

/-- `e ∉ cl X` when `X + e` lies in a basis and `e ∉ X`. -/
theorem notMem_closure_of_isBase {B X : Set α} {e : α} (hB : M.IsBase B) (h : insert e X ⊆ B)
    (he : e ∉ X) : e ∉ M.closure X :=
  notMem_closure_of_indep_insert (hB.indep.subset h) he

/-- `y ∈ cl {x, c₀, c₁}` when `{x, c₀, c₁, y}` is not a basis. -/
theorem mem_closure_of_not_isBase_last (hRank : M.eRank = 4) {x c0 c1 y : α}
    (hI : M.Indep {x, c0, c1}) (h1 : x ≠ c0) (h2 : x ≠ c1) (h3 : c0 ≠ c1) (hy : y ∈ M.E)
    (h : ¬ M.IsBase {x, c0, c1, y}) : y ∈ M.closure {x, c0, c1} := by
  by_contra hc
  exact h ((isBase4_iff_last hRank hI h1 h2 h3 hy).2 hc)

/-- `x ∈ cl {c₀, c₁, y}` when `{x, c₀, c₁, y}` is not a basis. -/
theorem mem_closure_of_not_isBase_first (hRank : M.eRank = 4) {x c0 c1 y : α}
    (hI : M.Indep {c0, c1, y}) (h1 : c0 ≠ c1) (h2 : c0 ≠ y) (h3 : c1 ≠ y) (hx : x ∈ M.E)
    (h : ¬ M.IsBase {x, c0, c1, y}) : x ∈ M.closure {c0, c1, y} := by
  by_contra hc
  exact h ((isBase4_iff_first hRank hI h1 h2 h3 hx).2 hc)

theorem mem_ground_of_isBase4 {B : Set α} (hB : M.IsBase B) {x : α} (hx : x ∈ B) : x ∈ M.E :=
  hB.subset_ground hx

/-! ### Splits and crossings -/

/-- A valid split: `A₀ ∪ P` and `Q ∪ A₁` are bases. -/
structure Valid (M : Matroid α) (a0 a1 b0 b1 p0 p1 q0 q1 : α) : Prop where
  valA : M.IsBase {a0, a1, p0, p1}
  valB : M.IsBase {q0, q1, b0, b1}

/-- `(P, Q)` is P-crossed, with `P` labelled `(u, v)`. -/
structure PCrossedAt (M : Matroid α) (a0 a1 b0 b1 u v q0 q1 : α) : Prop where
  x1 : u ∈ M.closure {b0, a0, a1}
  x2 : v ∈ M.closure {b1, a0, a1}
  x3 : b1 ∈ M.closure {u, q0, q1}
  x4 : b0 ∈ M.closure {v, q0, q1}

/-- `(P, Q)` is P-crossed. -/
def PCrossed (M : Matroid α) (a0 a1 b0 b1 p0 p1 q0 q1 : α) : Prop :=
  PCrossedAt M a0 a1 b0 b1 p0 p1 q0 q1 ∨ PCrossedAt M a0 a1 b0 b1 p1 p0 q0 q1

/-- `(P, Q)` is Q-crossed: P-crossed in the mirror. -/
def QCrossed (M : Matroid α) (a0 a1 b0 b1 p0 p1 q0 q1 : α) : Prop :=
  PCrossed M b0 b1 a0 a1 q0 q1 p0 p1

/-! ### Greene–Magnanti: a valid split exists -/

theorem exists_valid_split (hRank : M.eRank = 4) {a0 a1 b0 b1 : α} {S : Set α}
    (hB : M.IsBase {a0, a1, b0, b1}) (hS : M.IsBase S) (hdisj : Disjoint S {a0, a1, b0, b1}) :
    ∃ p0 p1 q0 q1, S = {p0, p1, q0, q1} ∧ Valid M a0 a1 b0 b1 p0 p1 q0 q1 := by
  obtain ⟨hab, ha0b0, ha0b1, ha1b0, ha1b1, hbb⟩ := distinct4 hRank hB
  have hA1 : ({a0, a1, b0, b1} : Set α) \ {b0} \ {b1} = {a0, a1} := by
    ext t
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨h | h | h | h, h2⟩, h3⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h2
      · exact absurd h h3
    · rintro (h | h)
      · subst h
        exact ⟨⟨Or.inl rfl, ha0b0⟩, ha0b1⟩
      · subst h
        exact ⟨⟨Or.inr (Or.inl rfl), ha1b0⟩, ha1b1⟩
  have hA2 : ({a0, a1, b0, b1} : Set α) \ {b1} \ {b0} = {a0, a1} := by
    rw [Set.sdiff_sdiff_comm]
    exact hA1
  obtain ⟨y1, hy1, y2, hy2, hy, hSP⟩ := KotlarZiv.exists_serialPair hB hS hdisj.symm
    (by simp : b0 ∈ ({a0, a1, b0, b1} : Set α)) (by simp : b1 ∈ ({a0, a1, b0, b1} : Set α)) hbb
  -- the other two elements of `S`
  have hS4 : S.ncard = 4 := KotlarZiv.ncard_eq_four hS hRank
  have hc1 : (S \ {y1}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem hy1, hS4]
  have hy2' : y2 ∈ S \ {y1} := ⟨hy2, fun h => hy (Set.mem_singleton_iff.1 h).symm⟩
  have hc2 : ((S \ {y1}) \ {y2}).ncard = 2 := by
    rw [Set.ncard_sdiff_singleton_of_mem hy2', hc1]
  obtain ⟨z1, z2, hz, hzeq⟩ := Set.ncard_eq_two.1 hc2
  have hSeq : S = {y1, y2, z1, z2} := by
    ext t
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · intro ht
      by_cases h1 : t = y1
      · exact Or.inl h1
      by_cases h2 : t = y2
      · exact Or.inr (Or.inl h2)
      have : t ∈ (S \ {y1}) \ {y2} := ⟨⟨ht, h1⟩, h2⟩
      rw [hzeq] at this
      simp only [mem_insert_iff, mem_singleton_iff] at this
      exact Or.inr (Or.inr this)
    · have hz1 : z1 ∈ S := by
        have : z1 ∈ (S \ {y1}) \ {y2} := by rw [hzeq]; simp
        exact this.1.1
      have hz2 : z2 ∈ S := by
        have : z2 ∈ (S \ {y1}) \ {y2} := by rw [hzeq]; simp
        exact this.1.1
      rintro (rfl | rfl | rfl | rfl)
      · exact hy1
      · exact hy2
      · exact hz1
      · exact hz2
  refine ⟨y1, y2, z1, z2, hSeq, ?_⟩
  rcases hSP with h | h
  · have h1 := h.base₂
    have h2 := h.base₂'
    rw [hA1] at h1
    rw [hzeq] at h2
    exact ⟨isBase_perm h1 (by set_perm'), isBase_perm h2 (by set_perm')⟩
  · have h1 := h.base₂
    have h2 := h.base₂'
    rw [hA2] at h1
    rw [hzeq] at h2
    exact ⟨isBase_perm h1 (by set_perm'), isBase_perm h2 (by set_perm')⟩

/-! ### The standing hypotheses: a P-crossed valid split -/

/-- A valid split `({u, v}, {w, z})`, P-crossed with the labelling `(u, v)`. -/
structure Std (M : Matroid α) (a0 a1 b0 b1 u v w z : α) : Prop where
  rank : M.eRank = 4
  hB : M.IsBase {a0, a1, b0, b1}
  hS : M.IsBase {u, v, w, z}
  hAP : M.IsBase {a0, a1, u, v}
  hQB : M.IsBase {w, z, b0, b1}
  X1 : u ∈ M.closure {b0, a0, a1}
  X2 : v ∈ M.closure {b1, a0, a1}
  X3 : b1 ∈ M.closure {u, w, z}
  X4 : b0 ∈ M.closure {v, w, z}

namespace Std

variable {a0 a1 b0 b1 u v w z : α}

/-- The twin symmetry `w ↔ z`. -/
theorem twin (h : Std M a0 a1 b0 b1 u v w z) : Std M a0 a1 b0 b1 u v z w where
  rank := h.rank
  hB := h.hB
  hS := isBase_perm h.hS (by set_perm')
  hAP := h.hAP
  hQB := isBase_perm h.hQB (by set_perm')
  X1 := h.X1
  X2 := h.X2
  X3 := mem_closure_perm h.X3 (by set_perm')
  X4 := mem_closure_perm h.X4 (by set_perm')

theorem mem (h : Std M a0 a1 b0 b1 u v w z) :
    a0 ∈ M.E ∧ a1 ∈ M.E ∧ b0 ∈ M.E ∧ b1 ∈ M.E ∧ u ∈ M.E ∧ v ∈ M.E ∧ w ∈ M.E ∧ z ∈ M.E :=
  ⟨h.hB.subset_ground (by simp), h.hB.subset_ground (by simp), h.hB.subset_ground (by simp),
    h.hB.subset_ground (by simp), h.hS.subset_ground (by simp), h.hS.subset_ground (by simp),
    h.hS.subset_ground (by simp), h.hS.subset_ground (by simp)⟩

/-- (D1) `b₁ ∉ H`. -/
theorem D1a (h : Std M a0 a1 b0 b1 u v w z) : b1 ∉ M.closure {b0, a0, a1} := by
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hB
  exact notMem_closure_of_isBase h.hB (by sub_perm) (by notin_tac)

/-- (D1) `b₀ ∉ H̄`. -/
theorem D1b (h : Std M a0 a1 b0 b1 u v w z) : b0 ∉ M.closure {b1, a0, a1} := by
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hB
  exact notMem_closure_of_isBase h.hB (by sub_perm) (by notin_tac)

/-- (D2) `u ∉ cl A₀`. -/
theorem D2u (h : Std M a0 a1 b0 b1 u v w z) : u ∉ M.closure {a0, a1} := by
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hAP
  exact notMem_closure_of_isBase h.hAP (by sub_perm) (by notin_tac)

/-- (D2) `v ∉ cl A₀`. -/
theorem D2v (h : Std M a0 a1 b0 b1 u v w z) : v ∉ M.closure {a0, a1} := by
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hAP
  exact notMem_closure_of_isBase h.hAP (by sub_perm) (by notin_tac)

/-- `H ∩ H̄ ⊆ cl A₀`. -/
theorem HH (h : Std M a0 a1 b0 b1 u v w z) {t : α} (h1 : t ∈ M.closure {b0, a0, a1})
    (h2 : t ∈ M.closure {b1, a0, a1}) : t ∈ M.closure {a0, a1} := by
  obtain ⟨ha0, ha1, -⟩ := h.mem
  exact mem_closure_of_mem_two (insert_subset ha0 (singleton_subset_iff.2 ha1)) h1 h2 h.D1a

/-- (X1) `cl(A₀ + u) = H`. -/
theorem H_eq (h : Std M a0 a1 b0 b1 u v w z) :
    M.closure {u, a0, a1} = M.closure {b0, a0, a1} :=
  Matroid.closure_insert_congr ⟨h.X1, h.D2u⟩

theorem b1_notMem_wz (h : Std M a0 a1 b0 b1 u v w z) : b1 ∉ M.closure {w, z} := by
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hQB
  exact notMem_closure_of_isBase h.hQB (by sub_perm) (by notin_tac)

theorem b0_notMem_wz (h : Std M a0 a1 b0 b1 u v w z) : b0 ∉ M.closure {w, z} := by
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hQB
  exact notMem_closure_of_isBase h.hQB (by sub_perm) (by notin_tac)

/-- (X3) `G = cl(u, w, z) = cl(w, z, b₁)`. -/
theorem G_eq (h : Std M a0 a1 b0 b1 u v w z) :
    M.closure {b1, w, z} = M.closure {u, w, z} :=
  Matroid.closure_insert_congr ⟨h.X3, h.b1_notMem_wz⟩

/-- (X4) `G' = cl(v, w, z) = cl(w, z, b₀)`. -/
theorem G'_eq (h : Std M a0 a1 b0 b1 u v w z) :
    M.closure {b0, w, z} = M.closure {v, w, z} :=
  Matroid.closure_insert_congr ⟨h.X4, h.b0_notMem_wz⟩

theorem X3' (h : Std M a0 a1 b0 b1 u v w z) : u ∈ M.closure {b1, w, z} := by
  rw [h.G_eq]
  exact M.mem_closure_of_mem' (by simp) h.mem.2.2.2.2.1

theorem X4' (h : Std M a0 a1 b0 b1 u v w z) : v ∈ M.closure {b0, w, z} := by
  rw [h.G'_eq]
  exact M.mem_closure_of_mem' (by simp) h.mem.2.2.2.2.2.1

theorem v_notMem_uwz (h : Std M a0 a1 b0 b1 u v w z) : v ∉ M.closure {u, w, z} := by
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hS
  exact notMem_closure_of_isBase h.hS (by sub_perm) (by notin_tac)

/-- **9.0.** `X_w` is valid if `w ∉ H` and `v ∉ cl(z, b₀, b₁)`. -/
theorem valid_of (h : Std M a0 a1 b0 b1 u v w z) (hw : w ∉ M.closure {b0, a0, a1})
    (hv : v ∉ M.closure {z, b0, b1}) : Valid M a0 a1 b0 b1 u w v z := by
  obtain ⟨ha0, ha1, hb0, hb1, hu, hv', hw', hz⟩ := h.mem
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hAP
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hQB
  refine ⟨?_, ?_⟩
  · have hI : M.Indep {u, a0, a1} := h.hAP.indep.subset (by sub_perm)
    have hb := (isBase_insert_iff h.rank hI (by ne_tac) (by ne_tac) (by ne_tac) hw').2
      (by rw [h.H_eq]; exact hw)
    exact isBase_perm hb (by set_perm')
  · have hI : M.Indep {z, b0, b1} := h.hQB.indep.subset (by sub_perm)
    exact (isBase_insert_iff h.rank hI (by ne_tac) (by ne_tac) (by ne_tac) hv').2 hv

theorem invalid (h : Std M a0 a1 b0 b1 u v w z) (hn : ¬ Valid M a0 a1 b0 b1 u w v z) :
    w ∈ M.closure {b0, a0, a1} ∨ v ∈ M.closure {z, b0, b1} := by
  by_contra hc
  push_neg at hc
  exact hn (h.valid_of hc.1 hc.2)

/-- **9.1.** `w` and `z` are not both in `H`. -/
theorem not_both_H (h : Std M a0 a1 b0 b1 u v w z) (hw : w ∈ M.closure {b0, a0, a1})
    (hz : z ∈ M.closure {b0, a0, a1}) : False := by
  have hsub : ({u, w, z} : Set α) ⊆ M.closure {b0, a0, a1} :=
    insert_subset h.X1 (insert_subset hw (singleton_subset_iff.2 hz))
  exact h.D1a (Matroid.closure_subset_closure_of_subset_closure hsub h.X3)

/-- **9.2.** If `v ∈ cl(w, b₀, b₁)`, then `v ∈ cl(w, b₀)`, `w ∉ H` and `w ∉ H̄`. -/
theorem claim92 (h : Std M a0 a1 b0 b1 u v w z) (hv : v ∈ M.closure {w, b0, b1}) :
    v ∈ M.closure {w, b0} ∧ w ∉ M.closure {b0, a0, a1} ∧ w ∉ M.closure {b1, a0, a1} := by
  obtain ⟨ha0, ha1, hb0, hb1, hu, hv', hw', hz⟩ := h.mem
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hQB
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hS
  have hvwb : v ∈ M.closure {w, b0} := by
    have hg : v ∈ M.closure (insert b1 {w, b0}) := mem_closure_perm hv (by set_perm')
    have hh : v ∈ M.closure (insert z {w, b0}) := mem_closure_perm h.X4' (by set_perm')
    have hne : z ∉ M.closure (insert b1 {w, b0}) :=
      notMem_closure_of_isBase h.hQB (by sub_perm) (by notin_tac)
    exact mem_closure_of_mem_two (insert_subset hw' (singleton_subset_iff.2 hb0)) hg hh hne
  refine ⟨hvwb, fun hw => ?_, fun hw => ?_⟩
  · have hb0H : b0 ∈ M.closure {b0, a0, a1} := M.mem_closure_of_mem' (by simp) hb0
    have hsub : ({w, b0} : Set α) ⊆ M.closure {b0, a0, a1} :=
      insert_subset hw (singleton_subset_iff.2 hb0H)
    have hvH := Matroid.closure_subset_closure_of_subset_closure hsub hvwb
    exact h.D2v (h.HH hvH h.X2)
  · have hvw : v ∉ M.closure {w} := notMem_closure_of_isBase h.hS (by sub_perm) (by notin_tac)
    have h1 : v ∈ M.closure (insert b0 {w}) := mem_closure_perm hvwb (by set_perm')
    have h2 : b0 ∈ M.closure (insert v {w}) := Matroid.mem_closure_insert hvw h1
    have hsub : (insert v {w} : Set α) ⊆ M.closure {b1, a0, a1} :=
      insert_subset h.X2 (singleton_subset_iff.2 hw)
    exact h.D1b (Matroid.closure_subset_closure_of_subset_closure hsub h2)

/-- **9.3.** `v ∈ cl(w, b₀, b₁)` and `v ∈ cl(z, b₀, b₁)` do not both hold. -/
theorem not_both_cl (h : Std M a0 a1 b0 b1 u v w z) (hw : v ∈ M.closure {w, b0, b1})
    (hz : v ∈ M.closure {z, b0, b1}) : False := by
  obtain ⟨ha0, ha1, hb0, hb1, hu, hv', hw', hz'⟩ := h.mem
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hQB
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hS
  have h1 : v ∈ M.closure (insert w {b0}) := (h.claim92 hw).1
  have h2 : v ∈ M.closure (insert z {b0}) := (h.twin.claim92 hz).1
  have hne : z ∉ M.closure (insert w {b0}) :=
    notMem_closure_of_isBase h.hQB (by sub_perm) (by notin_tac)
  have hvb : v ∈ M.closure {b0} := mem_closure_of_mem_two (singleton_subset_iff.2 hb0) h1 h2 hne
  have hv0 : v ∉ M.closure ∅ := by
    refine notMem_closure_of_isBase h.hS ?_ (notMem_empty v)
    rw [insert_emptyc_eq]
    exact singleton_subset_iff.2 (by simp)
  have h3 : v ∈ M.closure (insert b0 ∅) := by rw [insert_emptyc_eq]; exact hvb
  have h4 : b0 ∈ M.closure (insert v ∅) := Matroid.mem_closure_insert hv0 h3
  rw [insert_emptyc_eq] at h4
  have hsub : ({v} : Set α) ⊆ M.closure {b1, a0, a1} := singleton_subset_iff.2 h.X2
  exact h.D1b (Matroid.closure_subset_closure_of_subset_closure hsub h4)

/-- **9.4.** `X_w` or `X_z` is valid. -/
theorem valid_or (h : Std M a0 a1 b0 b1 u v w z) :
    Valid M a0 a1 b0 b1 u w v z ∨ Valid M a0 a1 b0 b1 u z v w := by
  by_contra hc
  push_neg at hc
  rcases h.invalid hc.1 with hw | hv <;> rcases h.twin.invalid hc.2 with hz | hv'
  · exact h.not_both_H hw hz
  · exact (h.claim92 hv').2.1 hw
  · exact (h.twin.claim92 hv).2.1 hz
  · exact h.not_both_cl hv' hv

/-- **9.5.** If `X_w` is valid and P-crossed, then `w ∈ H̄` and `u ∈ cl(z, b₁)`. -/
theorem claim95 (h : Std M a0 a1 b0 b1 u v w z) (hV : Valid M a0 a1 b0 b1 u w v z)
    (hP : PCrossed M a0 a1 b0 b1 u w v z) :
    w ∈ M.closure {b1, a0, a1} ∧ u ∈ M.closure {z, b1} := by
  obtain ⟨ha0, ha1, hb0, hb1, hu', hv', hw', hz'⟩ := h.mem
  rcases (show PCrossedAt M a0 a1 b0 b1 u w v z ∨ PCrossedAt M a0 a1 b0 b1 w u v z from hP)
    with hX | hX
  · refine ⟨hX.x2, ?_⟩
    obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank hV.valB
    have hb1vz : b1 ∉ M.closure {v, z} :=
      notMem_closure_of_isBase hV.valB (by sub_perm) (by notin_tac)
    have h1 : u ∈ M.closure (insert b1 {v, z}) := Matroid.mem_closure_insert hb1vz hX.x3
    have hg : u ∈ M.closure (insert w {z, b1}) := mem_closure_perm h.X3' (by set_perm')
    have hh : u ∈ M.closure (insert v {z, b1}) := mem_closure_perm h1 (by set_perm')
    have hne : v ∉ M.closure (insert w {z, b1}) := by
      intro hv
      have h2 : v ∈ M.closure {b1, w, z} := mem_closure_perm hv (by set_perm')
      rw [h.G_eq] at h2
      exact h.v_notMem_uwz h2
    exact mem_closure_of_mem_two (insert_subset hz' (singleton_subset_iff.2 hb1)) hg hh hne
  · exact (h.D2u (h.HH h.X1 hX.x2)).elim

/-- **9.6.** `X_w` and `X_z` are not both valid and P-crossed. -/
theorem not_both_crossed (h : Std M a0 a1 b0 b1 u v w z) (hVw : Valid M a0 a1 b0 b1 u w v z)
    (hPw : PCrossed M a0 a1 b0 b1 u w v z) (hVz : Valid M a0 a1 b0 b1 u z v w)
    (hPz : PCrossed M a0 a1 b0 b1 u z v w) : False := by
  have hw := (h.claim95 hVw hPw).1
  have hz := (h.twin.claim95 hVz hPz).1
  have hsub : ({v, w, z} : Set α) ⊆ M.closure {b1, a0, a1} :=
    insert_subset h.X2 (insert_subset hw (singleton_subset_iff.2 hz))
  exact h.D1b (Matroid.closure_subset_closure_of_subset_closure hsub h.X4)

/-- **9.7.** If `X_w` is valid and P-crossed, then `X_z` is valid. -/
theorem claim97 (h : Std M a0 a1 b0 b1 u v w z) (hVw : Valid M a0 a1 b0 b1 u w v z)
    (hPw : PCrossed M a0 a1 b0 b1 u w v z) : Valid M a0 a1 b0 b1 u z v w := by
  by_contra hnz
  obtain ⟨ha0, ha1, hb0, hb1, hu', hv', hw', hz'⟩ := h.mem
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 h.rank h.hS
  rcases h.twin.invalid hnz with hz | hv
  · have hu := (h.claim95 hVw hPw).2
    have huz : u ∉ M.closure {z} := notMem_closure_of_isBase h.hS (by sub_perm) (by notin_tac)
    have h1 : u ∈ M.closure (insert b1 {z}) := mem_closure_perm hu (by set_perm')
    have h2 : b1 ∈ M.closure (insert u {z}) := Matroid.mem_closure_insert huz h1
    have hsub : (insert u {z} : Set α) ⊆ M.closure {b0, a0, a1} :=
      insert_subset h.X1 (singleton_subset_iff.2 hz)
    exact h.D1a (Matroid.closure_subset_closure_of_subset_closure hsub h2)
  · exact (h.claim92 hv).2.2 (h.claim95 hVw hPw).1

theorem F1_of_valid (h : Std M a0 a1 b0 b1 u v w z) (hVw : Valid M a0 a1 b0 b1 u w v z) :
    (Valid M a0 a1 b0 b1 u w v z ∧ ¬ PCrossed M a0 a1 b0 b1 u w v z) ∨
      (Valid M a0 a1 b0 b1 u z v w ∧ ¬ PCrossed M a0 a1 b0 b1 u z v w) := by
  by_cases hPw : PCrossed M a0 a1 b0 b1 u w v z
  · exact Or.inr ⟨h.claim97 hVw hPw, fun hPz => h.not_both_crossed hVw hPw (h.claim97 hVw hPw) hPz⟩
  · exact Or.inl ⟨hVw, hPw⟩

/-- **Lemma F1.** `X_w` or `X_z` is valid and not P-crossed. -/
theorem F1 (h : Std M a0 a1 b0 b1 u v w z) :
    (Valid M a0 a1 b0 b1 u w v z ∧ ¬ PCrossed M a0 a1 b0 b1 u w v z) ∨
      (Valid M a0 a1 b0 b1 u z v w ∧ ¬ PCrossed M a0 a1 b0 b1 u z v w) := by
  rcases h.valid_or with hVw | hVz
  · exact h.F1_of_valid hVw
  · exact (h.twin.F1_of_valid hVz).symm

theorem F2core (h : Std M a0 a1 b0 b1 u v w z) {t t' : α}
    (hH : M.closure {t', t, b1} = M.closure {b1, a0, a1}) (ht : t ∈ M.E)
    (hv : v ∈ M.closure {t, b0, b1}) (htG : t ∈ M.closure {z, u, w}) : False := by
  obtain ⟨ha0, ha1, hb0, hb1, hu', hv', hw', hz'⟩ := h.mem
  have hg : v ∈ M.closure (insert t' {t, b1}) := by
    show v ∈ M.closure {t', t, b1}
    rw [hH]
    exact h.X2
  have hh : v ∈ M.closure (insert b0 {t, b1}) := mem_closure_perm hv (by set_perm')
  have hne : b0 ∉ M.closure (insert t' {t, b1}) := by
    show b0 ∉ M.closure {t', t, b1}
    rw [hH]
    exact h.D1b
  have hvt : v ∈ M.closure {t, b1} :=
    mem_closure_of_mem_two (insert_subset ht (singleton_subset_iff.2 hb1)) hg hh hne
  have hsub : ({t, b1} : Set α) ⊆ M.closure {u, w, z} :=
    insert_subset (mem_closure_perm htG (by set_perm')) (singleton_subset_iff.2 h.X3)
  exact h.v_notMem_uwz (Matroid.closure_subset_closure_of_subset_closure hsub hvt)

/-- **Lemma F2.** `X_w` is not Q-crossed. -/
theorem F2 (h : Std M a0 a1 b0 b1 u v w z) : ¬ QCrossed M a0 a1 b0 b1 u w v z := by
  obtain ⟨ha0, ha1, hb0, hb1, hu', hv', hw', hz'⟩ := h.mem
  intro hQ
  rcases (show PCrossedAt M b0 b1 a0 a1 v z u w ∨ PCrossedAt M b0 b1 a0 a1 z v u w from hQ)
    with hX | hX
  · exact h.F2core (t := a0) (t' := a1) (congrArg M.closure (by set_perm')) ha0 hX.x1 hX.x4
  · exact h.F2core (t := a1) (t' := a0) (congrArg M.closure (by set_perm')) ha1 hX.x2 hX.x3

/-- **The Key Lemma.** A P-crossed valid split has a one-swap that is valid and neither
P-crossed nor Q-crossed. -/
theorem key (h : Std M a0 a1 b0 b1 u v w z) :
    ∃ p0 p1 q0 q1, ({p0, p1, q0, q1} : Set α) = {u, v, w, z} ∧
      Valid M a0 a1 b0 b1 p0 p1 q0 q1 ∧ ¬ PCrossed M a0 a1 b0 b1 p0 p1 q0 q1 ∧
      ¬ QCrossed M a0 a1 b0 b1 p0 p1 q0 q1 := by
  rcases h.F1 with ⟨hV, hP⟩ | ⟨hV, hP⟩
  · exact ⟨u, w, v, z, by set_perm', hV, hP, h.F2⟩
  · exact ⟨u, z, v, w, by set_perm', hV, hP, h.twin.F2⟩

end Std

/-- The Key Lemma for any P-crossed valid split. -/
theorem key_of_pCrossed (hRank : M.eRank = 4) {a0 a1 b0 b1 x0 x1 y0 y1 : α}
    (hB : M.IsBase {a0, a1, b0, b1}) (hS : M.IsBase {x0, x1, y0, y1})
    (hV : Valid M a0 a1 b0 b1 x0 x1 y0 y1) (hP : PCrossed M a0 a1 b0 b1 x0 x1 y0 y1) :
    ∃ p0 p1 q0 q1, ({p0, p1, q0, q1} : Set α) = {x0, x1, y0, y1} ∧
      Valid M a0 a1 b0 b1 p0 p1 q0 q1 ∧ ¬ PCrossed M a0 a1 b0 b1 p0 p1 q0 q1 ∧
      ¬ QCrossed M a0 a1 b0 b1 p0 p1 q0 q1 := by
  rcases (show PCrossedAt M a0 a1 b0 b1 x0 x1 y0 y1 ∨ PCrossedAt M a0 a1 b0 b1 x1 x0 y0 y1
    from hP) with hX | hX
  · exact (Std.mk hRank hB hS hV.valA hV.valB hX.x1 hX.x2 hX.x3 hX.x4).key
  · obtain ⟨p0, p1, q0, q1, he, hr⟩ := (Std.mk hRank hB (isBase_perm hS (by set_perm'))
      (isBase_perm hV.valA (by set_perm')) hV.valB hX.x1 hX.x2 hX.x3 hX.x4).key
    exact ⟨p0, p1, q0, q1, he.trans (by set_perm'), hr⟩

/-- **The Main Lemma.** Some valid split is neither P-crossed nor Q-crossed. -/
theorem main_lemma (hRank : M.eRank = 4) {a0 a1 b0 b1 : α} {S : Set α}
    (hB : M.IsBase {a0, a1, b0, b1}) (hS : M.IsBase S) (hdisj : Disjoint S {a0, a1, b0, b1}) :
    ∃ p0 p1 q0 q1, S = {p0, p1, q0, q1} ∧ Valid M a0 a1 b0 b1 p0 p1 q0 q1 ∧
      ¬ PCrossed M a0 a1 b0 b1 p0 p1 q0 q1 ∧ ¬ QCrossed M a0 a1 b0 b1 p0 p1 q0 q1 := by
  obtain ⟨p0, p1, q0, q1, hSeq, hV⟩ := exists_valid_split hRank hB hS hdisj
  have hS' : M.IsBase {p0, p1, q0, q1} := hSeq ▸ hS
  by_cases hP : PCrossed M a0 a1 b0 b1 p0 p1 q0 q1
  · obtain ⟨x0, x1, y0, y1, he, hr⟩ := key_of_pCrossed hRank hB hS' hV hP
    exact ⟨x0, x1, y0, y1, hSeq.trans he.symm, hr⟩
  by_cases hQ : QCrossed M a0 a1 b0 b1 p0 p1 q0 q1
  · -- the mirror
    have hB' : M.IsBase {b0, b1, a0, a1} := isBase_perm hB (by set_perm')
    have hS'' : M.IsBase {q0, q1, p0, p1} := isBase_perm hS' (by set_perm')
    have hV' : Valid M b0 b1 a0 a1 q0 q1 p0 p1 :=
      ⟨isBase_perm hV.valB (by set_perm'), isBase_perm hV.valA (by set_perm')⟩
    obtain ⟨x0, x1, y0, y1, he, hV'', hP'', hQ''⟩ := key_of_pCrossed hRank hB' hS'' hV' hQ
    refine ⟨y0, y1, x0, x1, ?_, ⟨isBase_perm hV''.valB (by set_perm'),
      isBase_perm hV''.valA (by set_perm')⟩, hQ'', hP''⟩
    rw [hSeq, show ({y0, y1, x0, x1} : Set α) = {x0, x1, y0, y1} by set_perm', he]
    set_perm'
  · exact ⟨p0, p1, q0, q1, hSeq, hV, hP, hQ⟩

end HigherRankKUM.XP
