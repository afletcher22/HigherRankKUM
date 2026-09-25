import Probe.VHT.Statement

/-!
# Theorem 2.1, step 2: pushes

An element `e` is *pushable* for `φ` when it lies in the closure of the other elements covering
its first point `φ e`, that is, when it lies in a circuit there. A *push* moves its arc forward
by one. When every weight is below `D`:

* a push removes `e` only from its first point, and there `e` is already spanned by the rest; so
  no closure `cl(E_φ(x))` shrinks (`closure_push`);
* going back from a point that covers a nonempty set `C`, the last point still covering `C` is
  the first point of some element of `C` (`exists_start`);
* every dependent point set contains a pushable element (`exists_pushable`).
-/

namespace HigherRankKUM.VHT

open Set

variable {α : Type*} [DecidableEq α] {M : Matroid α} {D : ℕ} [NeZero D] {ω : α → ℕ}

/-- `e` is pushable for `φ`: it is spanned by the other elements covering its first point. -/
def Pushable (M : Matroid α) (φ : α → ZMod D) (ω : α → ℕ) (e : α) : Prop :=
  e ∈ M.closure (arcSet M φ ω (φ e) \ {e})

/-- Push `e` one step forward. -/
def push (φ : α → ZMod D) (e : α) : α → ZMod D := Function.update φ e (φ e + 1)

/-! ### Arithmetic on `ZMod D` -/

theorem val_sub_one_of_ne_zero {a : ZMod D} (ha : a ≠ 0) : (a - 1).val = a.val - 1 := by
  have h1 : 1 ≤ a.val := by
    by_contra h
    exact ha ((ZMod.val_eq_zero a).1 (by omega))
  have h2 : a - 1 = ((a.val - 1 : ℕ) : ZMod D) := by
    rw [Nat.cast_sub h1, ZMod.natCast_zmod_val, Nat.cast_one]
  rw [h2, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt a; omega)]

theorem val_neg_one' : ((-1 : ZMod D)).val = D - 1 := by
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have h : (-1 : ZMod D) = ((D - 1 : ℕ) : ZMod D) := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-! ### Membership after a push -/

theorem push_apply_self (φ : α → ZMod D) (e : α) : push φ e e = φ e + 1 := by
  simp [push]

theorem push_apply_ne (φ : α → ZMod D) {e f : α} (h : f ≠ e) : push φ e f = φ f := by
  simp [push, h]

/-- An element never covers the point just before its first point. -/
theorem not_mem_arcSet_pred (hω : ∀ e ∈ M.E, ω e < D) (φ : α → ZMod D) (e : α) :
    e ∉ arcSet M φ ω (φ e - 1) := by
  rintro ⟨he, h⟩
  have := hω e he
  rw [sub_sub_cancel_left, val_neg_one'] at h
  omega

/-- If `x` is not the first point of `e`, a push keeps everything that covered `x`. -/
theorem arcSet_subset_push (φ : α → ZMod D) (e : α) {x : ZMod D} (hx : x ≠ φ e) :
    arcSet M φ ω x ⊆ arcSet M (push φ e) ω x := by
  rintro f ⟨hf, h⟩
  refine ⟨hf, ?_⟩
  by_cases hfe : f = e
  · subst hfe
    rw [push_apply_self, ← sub_sub, val_sub_one_of_ne_zero (sub_ne_zero.2 hx)]
    omega
  · rwa [push_apply_ne φ hfe]

/-- At its own first point, a push removes exactly `e`. -/
theorem arcSet_push_self (hω : ∀ e ∈ M.E, ω e < D) (φ : α → ZMod D) (e : α) :
    arcSet M (push φ e) ω (φ e) = arcSet M φ ω (φ e) \ {e} := by
  ext f
  by_cases hfe : f = e
  · subst hfe
    simp only [mem_diff, mem_singleton_iff, not_true_eq_false, and_false, iff_false]
    have h := not_mem_arcSet_pred (M := M) hω (push φ f) f
    rwa [push_apply_self, add_sub_cancel_right] at h
  · simp only [arcSet, mem_setOf_eq, mem_diff, mem_singleton_iff, hfe, not_false_eq_true,
      and_true, push_apply_ne φ hfe]

/-- A push of a pushable element never shrinks a closure. -/
theorem closure_push (hω : ∀ e ∈ M.E, ω e < D) (φ : α → ZMod D) {e : α}
    (hp : Pushable M φ ω e) (x : ZMod D) :
    M.closure (arcSet M φ ω x) ⊆ M.closure (arcSet M (push φ e) ω x) := by
  by_cases hx : x = φ e
  · subst hx
    rw [arcSet_push_self hω, Matroid.closure_sdiff_singleton_eq_closure hp]
  · exact M.closure_subset_closure (arcSet_subset_push φ e hx)

/-! ### Walking back -/

/-- Going back from a point covering a nonempty set `C`, the last point still covering `C` is the
first point of some element of `C`. -/
theorem exists_start (hω : ∀ e ∈ M.E, ω e < D) (φ : α → ZMod D) {C : Set α}
    (hCne : C.Nonempty) {x : ZMod D} (hx : C ⊆ arcSet M φ ω x) :
    ∃ e ∈ C, C ⊆ arcSet M φ ω (φ e) := by
  classical
  obtain ⟨e0, he0⟩ := hCne
  have hex : ∃ t : ℕ, ¬ C ⊆ arcSet M φ ω (x - t) := by
    refine ⟨(x - (φ e0 - 1)).val, fun h => ?_⟩
    have h' := h he0
    rw [ZMod.natCast_zmod_val, sub_sub_cancel] at h'
    exact not_mem_arcSet_pred hω φ e0 h'
  let t0 := Nat.find hex
  have ht0 : ¬ C ⊆ arcSet M φ ω (x - t0) := Nat.find_spec hex
  have ht0pos : 0 < t0 := by
    rcases Nat.eq_zero_or_pos t0 with h | h
    · rw [h] at ht0
      simp only [Nat.cast_zero, sub_zero] at ht0
      exact absurd hx ht0
    · exact h
  have hprev : C ⊆ arcSet M φ ω (x - (t0 - 1 : ℕ)) := by
    have := Nat.find_min hex (show t0 - 1 < t0 by omega)
    push_neg at this
    exact this
  obtain ⟨e, heC, he⟩ := not_subset.1 ht0
  refine ⟨e, heC, ?_⟩
  have hy : x - ((t0 - 1 : ℕ) : ZMod D) = φ e := by
    by_contra hne
    apply he
    have hmem := hprev heC
    refine ⟨hmem.1, ?_⟩
    have hsplit : x - (t0 : ZMod D) - φ e = x - ((t0 - 1 : ℕ) : ZMod D) - φ e - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      ring
    rw [hsplit, val_sub_one_of_ne_zero (sub_ne_zero.2 hne)]
    have := hmem.2
    omega
  rw [← hy]
  exact hprev

/-- A dependent point set contains a pushable element. -/
theorem exists_pushable (hω : ∀ e ∈ M.E, ω e < D) (φ : α → ZMod D) {x : ZMod D}
    (hdep : ¬ M.Indep (arcSet M φ ω x)) : ∃ e ∈ M.E, Pushable M φ ω e := by
  obtain ⟨C, hCx, hC⟩ :=
    ((Matroid.not_indep_iff (arcSet_subset M φ ω x)).1 hdep).exists_isCircuit_subset
  obtain ⟨e, heC, hCe⟩ := exists_start hω φ hC.nonempty hCx
  refine ⟨e, (hCx heC).1, ?_⟩
  exact M.closure_subset_closure (diff_subset_diff_left hCe)
    (hC.mem_closure_sdiff_singleton_of_mem heC)

end HigherRankKUM.VHT
