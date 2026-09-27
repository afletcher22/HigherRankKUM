import Probe.Rank4.SerialExchange
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Set.Card

/-!
# Pair-chain insertion (XP): basic tools

Rank-4 facts about small sets, used throughout the XP modules:

* `distinct4`: the four elements of a basis are distinct;
* `isBase_insert_iff`, `isBase4_iff_last`, `isBase4_iff_first`: a 4-set that extends an
  independent 3-set is a basis exactly when the new element is outside the closure of the 3-set;
* `false_of_subset_closure3`: a basis does not lie in the closure of three elements;
* `mem_closure_of_mem_two`: two distinct flats `cl(X + g)` and `cl(X + h)` meet in `cl X`
  (exchange);
* `exists_isBase_augment`, `exists_isBase_augment_first`: augmentation of a 3-set from a basis.

And Boolean relations on `Bool × Bool`: `Slack` (at most one missing entry) and `Good`.
-/

namespace HigherRankKUM.XP

open Set

/-- Equality of set literals up to order; `!false` and `!true` are evaluated first. -/
macro "set_perm'" : tactic =>
  `(tactic| (ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Bool.not_false,
    Bool.not_true]; try tauto))

/-- Inclusion of set literals. -/
macro "sub_perm" : tactic =>
  `(tactic| (intro t ht; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢; try tauto))

variable {α : Type*} {M : Matroid α}

/-! ### Small sets -/

theorem encard_three_le (x y z : α) : ({x, y, z} : Set α).encard ≤ 3 := by
  calc ({x, y, z} : Set α).encard ≤ ({y, z} : Set α).encard + 1 := encard_insert_le _ _
    _ ≤ (({z} : Set α).encard + 1) + 1 := by gcongr; exact encard_insert_le _ _
    _ = 3 := by rw [encard_singleton]; norm_num

theorem encard_three_eq {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Set α).encard = 3 := by
  have hx : x ∉ ({y, z} : Set α) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hxy, hxz⟩
  rw [encard_insert_of_notMem hx, encard_pair hyz]
  norm_num

/-- The four elements of a basis of a rank-4 matroid are distinct. -/
theorem distinct4 (hRank : M.eRank = 4) {a b c d : α} (h : M.IsBase {a, b, c, d}) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have h4 : ({a, b, c, d} : Set α).encard = 4 := by rw [h.encard_eq_eRank, hRank]
  have key : ∀ x y z : α, ({a, b, c, d} : Set α) ⊆ {x, y, z} → False := by
    intro x y z hs
    have h3 := (encard_le_encard hs).trans (encard_three_le x y z)
    rw [h4] at h3
    exact absurd h3 (by norm_num)
  refine ⟨fun e => key b c d ?_, fun e => key b c d ?_, fun e => key b c d ?_,
    fun e => key a c d ?_, fun e => key a c d ?_, fun e => key a b d ?_⟩ <;> rw [e] <;> sub_perm

/-- A 3-set `{x, y, z}` of distinct independent elements of a rank-4 matroid: adding `e` gives a
basis exactly when `e ∉ cl {x, y, z}`. -/
theorem isBase_insert_iff (hRank : M.eRank = 4) {x y z e : α} (hI : M.Indep {x, y, z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (he : e ∈ M.E) :
    M.IsBase (insert e {x, y, z}) ↔ e ∉ M.closure {x, y, z} := by
  have h3 := encard_three_eq hxy hxz hyz
  constructor
  · intro hB
    have heI : e ∉ ({x, y, z} : Set α) := by
      intro hmem
      rw [insert_eq_of_mem hmem] at hB
      have h4 := hB.encard_eq_eRank
      rw [h3, hRank] at h4
      exact absurd h4 (by norm_num)
    exact ((hI.insert_indep_iff_of_notMem heI).1 hB.indep).2
  · intro hcl
    have heI : e ∉ ({x, y, z} : Set α) := fun hmem =>
      hcl (M.subset_closure _ hI.subset_ground hmem)
    have hind : M.Indep (insert e {x, y, z}) := (hI.insert_indep_iff_of_notMem heI).2 ⟨he, hcl⟩
    refine hind.isBase_of_eRk_ge (Set.toFinite _) ?_
    rw [hind.eRk_eq_encard, encard_insert_of_notMem heI, h3, hRank]
    norm_num

/-- `{x, c₀, c₁, y}` is a basis iff `y ∉ cl {x, c₀, c₁}`. -/
theorem isBase4_iff_last (hRank : M.eRank = 4) {x c0 c1 y : α} (hI : M.Indep {x, c0, c1})
    (h1 : x ≠ c0) (h2 : x ≠ c1) (h3 : c0 ≠ c1) (hy : y ∈ M.E) :
    M.IsBase {x, c0, c1, y} ↔ y ∉ M.closure {x, c0, c1} := by
  have heq : ({x, c0, c1, y} : Set α) = insert y {x, c0, c1} := by set_perm'
  rw [heq]
  exact isBase_insert_iff hRank hI h1 h2 h3 hy

/-- `{x, c₀, c₁, y}` is a basis iff `x ∉ cl {c₀, c₁, y}`. -/
theorem isBase4_iff_first (hRank : M.eRank = 4) {x c0 c1 y : α} (hI : M.Indep {c0, c1, y})
    (h1 : c0 ≠ c1) (h2 : c0 ≠ y) (h3 : c1 ≠ y) (hx : x ∈ M.E) :
    M.IsBase {x, c0, c1, y} ↔ x ∉ M.closure {c0, c1, y} :=
  isBase_insert_iff hRank hI h1 h2 h3 hx

/-- A basis does not lie in the closure of three elements. -/
theorem false_of_subset_closure3 (hRank : M.eRank = 4) {B : Set α} (hB : M.IsBase B)
    {x y z : α} (h : B ⊆ M.closure {x, y, z}) : False := by
  have h1 := M.eRk_mono h
  rw [M.eRk_closure_eq, hB.eRk_eq_eRank, hRank] at h1
  have h2 := h1.trans ((M.eRk_le_encard {x, y, z}).trans (encard_three_le x y z))
  exact absurd h2 (by norm_num)

/-- Two flats `cl(X + g)` and `cl(X + h)` with `h ∉ cl(X + g)` meet in `cl X`. -/
theorem mem_closure_of_mem_two {X : Set α} {g h z : α} (hX : X ⊆ M.E)
    (hg : z ∈ M.closure (insert g X)) (hh : z ∈ M.closure (insert h X))
    (hne : h ∉ M.closure (insert g X)) : z ∈ M.closure X := by
  by_contra hz
  have h1 : h ∈ M.closure (insert z X) := Matroid.mem_closure_insert hz hh
  have h2 : insert z X ⊆ M.closure (insert g X) :=
    insert_subset hg ((M.subset_closure X hX).trans (M.closure_subset_closure (subset_insert g X)))
  exact hne (Matroid.closure_subset_closure_of_subset_closure h2 h1)

/-- Augmentation of `{u, c₀, c₁}` from the basis `{c₀, c₁, w₀, w₁}`. -/
theorem exists_isBase_augment (hRank : M.eRank = 4) {u c0 c1 w0 w1 : α}
    (hI : M.Indep {u, c0, c1}) (h1 : u ≠ c0) (h2 : u ≠ c1) (h3 : c0 ≠ c1)
    (hB : M.IsBase {c0, c1, w0, w1}) :
    M.IsBase {u, c0, c1, w0} ∨ M.IsBase {u, c0, c1, w1} := by
  have h3' := encard_three_eq h1 h2 h3
  have hnb : ¬ M.IsBase {u, c0, c1} := by
    intro hb
    have h4 := hb.encard_eq_eRank
    rw [h3', hRank] at h4
    exact absurd h4 (by norm_num)
  obtain ⟨e, he, hind⟩ := hI.exists_insert_of_not_isBase hnb hB
  have heI : e ∉ ({u, c0, c1} : Set α) := he.2
  have hcl : e ∉ M.closure {u, c0, c1} := ((hI.insert_indep_iff_of_notMem heI).1 hind).2
  have heE : e ∈ M.E := hB.subset_ground he.1
  have hmem : e = c0 ∨ e = c1 ∨ e = w0 ∨ e = w1 := by
    have := he.1
    simpa only [mem_insert_iff, mem_singleton_iff] using this
  rcases hmem with rfl | rfl | rfl | rfl
  · exact (heI (by simp)).elim
  · exact (heI (by simp)).elim
  · exact Or.inl ((isBase4_iff_last hRank hI h1 h2 h3 heE).2 hcl)
  · exact Or.inr ((isBase4_iff_last hRank hI h1 h2 h3 heE).2 hcl)

/-- Augmentation of `{c₀, c₁, w}` from the basis `{u₀, u₁, c₀, c₁}`. -/
theorem exists_isBase_augment_first (hRank : M.eRank = 4) {w c0 c1 u0 u1 : α}
    (hI : M.Indep {c0, c1, w}) (h1 : c0 ≠ c1) (h2 : c0 ≠ w) (h3 : c1 ≠ w)
    (hB : M.IsBase {u0, u1, c0, c1}) :
    M.IsBase {u0, c0, c1, w} ∨ M.IsBase {u1, c0, c1, w} := by
  have h3' := encard_three_eq h1 h2 h3
  have hnb : ¬ M.IsBase {c0, c1, w} := by
    intro hb
    have h4 := hb.encard_eq_eRank
    rw [h3', hRank] at h4
    exact absurd h4 (by norm_num)
  obtain ⟨e, he, hind⟩ := hI.exists_insert_of_not_isBase hnb hB
  have heI : e ∉ ({c0, c1, w} : Set α) := he.2
  have hcl : e ∉ M.closure {c0, c1, w} := ((hI.insert_indep_iff_of_notMem heI).1 hind).2
  have heE : e ∈ M.E := hB.subset_ground he.1
  have hmem : e = u0 ∨ e = u1 ∨ e = c0 ∨ e = c1 := by
    have := he.1
    simpa only [mem_insert_iff, mem_singleton_iff] using this
  rcases hmem with rfl | rfl | rfl | rfl
  · exact Or.inl ((isBase4_iff_first hRank hI h1 h2 h3 heE).2 hcl)
  · exact Or.inr ((isBase4_iff_first hRank hI h1 h2 h3 heE).2 hcl)
  · exact (heI (by simp)).elim
  · exact (heI (by simp)).elim

/-- The two orderings of a pair, as sets. -/
theorem pair_set_eq (u v : Bool → α) (a b : Bool) :
    ({u a, u (!a), v b, v (!b)} : Set α) = {u false, u true, v false, v true} := by
  cases a <;> cases b <;> set_perm'

/-- A window with its middle pair in either order. -/
theorem win_set_eq (x y : α) (v : Bool → α) (b : Bool) :
    ({x, v b, v (!b), y} : Set α) = {x, v false, v true, y} := by
  cases b <;> set_perm'

/-! ### Boolean relations -/

/-- A relation on `Bool × Bool` with at most one missing entry. -/
def Slack (R : Bool → Bool → Prop) : Prop := ∀ a b c d, ¬ R a b → ¬ R c d → a = c ∧ b = d

/-- A slack relation closes a cycle: some `c` has `R (F c) c`. -/
theorem slack_close {R : Bool → Bool → Prop} (h : Slack R) (F : Bool → Bool) :
    ∃ c, R (F c) c := by
  by_contra hno
  push_neg at hno
  exact Bool.false_ne_true (h (F false) false (F true) true (hno false) (hno true)).2

/-- A relation with full support that is not slack and contains `(false, false)` is the
identity: it misses exactly `(false, true)` and `(true, false)`. -/
theorem tight_of_not_slack {R : Bool → Bool → Prop} (hff : R false false)
    (hr : R true false ∨ R true true) (hc : R false true ∨ R true true) (h : ¬ Slack R) :
    ¬ R false true ∧ ¬ R true false := by
  simp only [Slack] at h
  push_neg at h
  obtain ⟨a, b, c, d, h1, h2, h3⟩ := h
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- Both diagonal values hold, or at most one of the four values fails. -/
def Good (T : Bool → Bool → Prop) : Prop :=
  (T false false ∧ T true true) ∨
    ((T false false ∨ T false true) ∧ (T false false ∨ T true false) ∧
      (T false false ∨ T true true) ∧ (T false true ∨ T true false) ∧
      (T false true ∨ T true true) ∧ (T true false ∨ T true true))

theorem Good.diag {T : Bool → Bool → Prop} (h : Good T) : ∃ e, T e e := by
  rcases h with ⟨h1, -⟩ | ⟨-, -, h3, -, -, -⟩
  · exact ⟨false, h1⟩
  · rcases h3 with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩

theorem Good.common {T U : Bool → Bool → Prop} (hT : Good T) (hU : Good U) :
    ∃ e1 e2, T e1 e2 ∧ U e1 e2 := by
  rcases hT with ⟨t1, t2⟩ | ⟨t1, t2, t3, t4, t5, t6⟩
  · rcases hU with ⟨u1, u2⟩ | ⟨u1, u2, u3, u4, u5, u6⟩
    · exact ⟨false, false, t1, u1⟩
    · rcases u3 with u | u
      · exact ⟨false, false, t1, u⟩
      · exact ⟨true, true, t2, u⟩
  · rcases hU with ⟨u1, u2⟩ | ⟨u1, u2, u3, u4, u5, u6⟩
    · rcases t3 with t | t
      · exact ⟨false, false, t, u1⟩
      · exact ⟨true, true, t, u2⟩
    · by_cases a : T false false
      · by_cases b : U false false
        · exact ⟨false, false, a, b⟩
        · have b1 : U false true := u1.resolve_left b
          have b2 : U true false := u2.resolve_left b
          rcases t4 with t | t
          · exact ⟨false, true, t, b1⟩
          · exact ⟨true, false, t, b2⟩
      · have a1 : T false true := t1.resolve_left a
        have a2 : T true false := t2.resolve_left a
        rcases u4 with u | u
        · exact ⟨false, true, a1, u⟩
        · exact ⟨true, false, a2, u⟩

theorem Good.mono {T U : Bool → Bool → Prop} (h : ∀ a b, T a b → U a b) (hT : Good T) :
    Good U := by
  rcases hT with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl ⟨h _ _ h1, h _ _ h2⟩
  · exact Or.inr ⟨h1.imp (h _ _) (h _ _), h2.imp (h _ _) (h _ _), h3.imp (h _ _) (h _ _),
      h4.imp (h _ _) (h _ _), h5.imp (h _ _) (h _ _), h6.imp (h _ _) (h _ _)⟩

theorem Good.swap {T : Bool → Bool → Prop} (h : Good T) : Good (fun a b => T b a) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1, h3, h4.symm, h6, h5⟩

/-- The pair constraint of one side: `T(u, w)` holds when some `o` has `r(o, !u)` and
`s(!o, w)`. -/
def TT (r s : Bool → Bool → Prop) (u w : Bool) : Prop := ∃ o, r o (!u) ∧ s (!o) w

/-- **Claims 4.1 and 5.1–5.2 of the local lemmas, one side.** If the non-entries of `r` and of
`s` are matchings (no row or column of either is empty) and they do not form a crossing, then
`TT r s` is `Good`. -/
theorem good_TT {r s : Bool → Bool → Prop}
    (hr1 : ∀ i, r i false ∨ r i true) (hr2 : ∀ j, r false j ∨ r true j)
    (hs1 : ∀ i, s i false ∨ s i true) (hs2 : ∀ j, s false j ∨ s true j)
    (hc : ¬ ∃ i, ¬ r i false ∧ ¬ r (!i) true ∧ ¬ s i true ∧ ¬ s (!i) false) :
    Good (TT r s) := by
  have a1 := hr1 false
  have a2 := hr1 true
  have a3 := hr2 false
  have a4 := hr2 true
  have b1 := hs1 false
  have b2 := hs1 true
  have b3 := hs2 false
  have b4 := hs2 true
  have c1 : ¬ (¬ r false false ∧ ¬ r true true ∧ ¬ s false true ∧ ¬ s true false) :=
    fun h => hc ⟨false, h⟩
  have c2 : ¬ (¬ r true false ∧ ¬ r false true ∧ ¬ s true true ∧ ¬ s false false) :=
    fun h => hc ⟨true, h⟩
  clear hr1 hr2 hs1 hs2 hc
  simp only [Good, TT, Bool.exists_bool, Bool.not_false, Bool.not_true]
  by_cases p1 : r false false <;> by_cases p2 : r false true <;> by_cases p3 : r true false <;>
    by_cases p4 : r true true <;> by_cases q1 : s false false <;> by_cases q2 : s false true <;>
    by_cases q3 : s true false <;> by_cases q4 : s true true <;> simp_all

end HigherRankKUM.XP
