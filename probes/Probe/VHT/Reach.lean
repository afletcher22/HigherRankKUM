import Probe.VHT.Best

/-!
# Theorem 2.1, steps 3–4: the push graph and a sink component

The mappings reachable from `φ` by pushes form a finite directed graph: pushes only change values
on the ground set. Pick a reachable `η` whose own reachable set is as small as possible. Then
every state reachable from `η` can reach `η` back: `η` lies in a sink component. This replaces
the paper's ordered push sequence.

* An element pushed somewhere in the component is *unbounded*. Following a closed walk, its
  first point passes through every point of the `D`-gon (`visits`).
* An element never pushed there is *bounded*. By definition it is never pushable in the
  component, which is the paper's Claim 2, and its first point never moves.
-/

namespace HigherRankKUM.VHT

open Set

variable {α : Type*} [DecidableEq α] {M : Matroid α} {D : ℕ} [NeZero D] {ω : α → ℕ}

/-- One push of a pushable ground-set element. -/
def PushStep (M : Matroid α) (ω : α → ℕ) (φ ψ : α → ZMod D) : Prop :=
  ∃ e ∈ M.E, Pushable M φ ω e ∧ ψ = push φ e

/-- Reachability by pushes. -/
abbrev Reach (M : Matroid α) (ω : α → ℕ) : (α → ZMod D) → (α → ZMod D) → Prop :=
  Relation.ReflTransGen (PushStep M ω)

theorem reach_off_ground {φ ψ : α → ZMod D} (h : Reach M ω φ ψ) : ∀ a ∉ M.E, ψ a = φ a := by
  induction h with
  | refl => intro a _; rfl
  | tail _ hstep ih =>
    intro a ha
    obtain ⟨e, he, -, rfl⟩ := hstep
    have hae : a ≠ e := by
      rintro rfl
      exact ha he
    rw [push_apply_ne _ hae, ih a ha]

theorem reach_isBest (hE : M.E.Finite) (hω : ∀ e ∈ M.E, ω e < D) {φ ψ : α → ZMod D}
    (hb : IsBest M φ ω) (h : Reach M ω φ ψ) :
    IsBest M ψ ω ∧ ∀ x, M.closure (arcSet M ψ ω x) = M.closure (arcSet M φ ω x) := by
  induction h with
  | refl => exact ⟨hb, fun _ => rfl⟩
  | tail _ hstep ih =>
    obtain ⟨e, -, hp, rfl⟩ := hstep
    exact ⟨push_isBest hE hω ih.1 hp, fun x => (push_closure_eq hE hω ih.1 hp x).trans (ih.2 x)⟩

theorem finite_reach (hE : M.E.Finite) (φ : α → ZMod D) : {ψ | Reach M ω φ ψ}.Finite := by
  haveI : Finite M.E := hE.to_subtype
  refine (Set.finite_range fun g : M.E → ZMod D => extendGround M g φ).subset fun ψ hψ => ?_
  refine ⟨fun e => ψ e, funext fun a => ?_⟩
  show extendGround M (fun e : M.E => ψ e) φ a = ψ a
  by_cases ha : a ∈ M.E
  · exact extendGround_apply ha
  · rw [extendGround_apply_not_mem ha, reach_off_ground hψ a ha]

/-- A reachable state in a sink component. -/
theorem exists_sink (hE : M.E.Finite) (φ : α → ZMod D) :
    ∃ η, Reach M ω φ η ∧ ∀ ψ, Reach M ω η ψ → Reach M ω ψ η := by
  obtain ⟨η, hη, hmin⟩ := Set.exists_min_image {ψ | Reach M ω φ ψ}
    (fun ψ => {χ | Reach M ω ψ χ}.ncard) (finite_reach hE φ) ⟨φ, Relation.ReflTransGen.refl⟩
  refine ⟨η, hη, fun ψ hψ => ?_⟩
  have hsub : {χ | Reach M ω ψ χ} ⊆ {χ | Reach M ω η χ} := fun χ hχ => hψ.trans hχ
  have hle : {χ | Reach M ω η χ}.ncard ≤ {χ | Reach M ω ψ χ}.ncard :=
    hmin ψ (show Reach M ω φ ψ from hη.trans hψ)
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (finite_reach hE η)
  have hmem : η ∈ {χ | Reach M ω ψ χ} := by
    rw [heq]
    exact Relation.ReflTransGen.refl
  exact hmem

/-- Along a push path, the first point of `f` moves forward one step at a time, so every value
from the start up to the total number of steps is attained. -/
theorem reach_values (f : α) {a b : α → ZMod D} (h : Reach M ω a b) :
    ∃ N : ℕ, (N : ZMod D) = b f - a f ∧ ∀ j ≤ N, ∃ c, Reach M ω a c ∧ c f = a f + j := by
  induction h with
  | refl =>
    refine ⟨0, by simp, fun j hj => ⟨a, Relation.ReflTransGen.refl, ?_⟩⟩
    rw [Nat.le_zero.1 hj]
    simp
  | @tail b c hab hbc ih =>
    obtain ⟨N, hN, hj⟩ := ih
    obtain ⟨e, he, hp, rfl⟩ := hbc
    by_cases hfe : f = e
    · subst hfe
      refine ⟨N + 1, ?_, fun j hjN => ?_⟩
      · rw [push_apply_self]
        push_cast
        rw [hN]
        ring
      · rcases Nat.lt_or_ge j (N + 1) with hlt | hge
        · exact hj j (by omega)
        · refine ⟨push b f, hab.tail ⟨f, he, hp, rfl⟩, ?_⟩
          have hjN1 : j = N + 1 := by omega
          rw [push_apply_self, hjN1]
          have hbf : b f = a f + N := by rw [hN]; ring
          rw [hbf]
          push_cast
          ring
    · refine ⟨N, ?_, fun j hjN => ?_⟩
      · rw [push_apply_ne _ hfe]
        exact hN
      · obtain ⟨c', hc', hc'f⟩ := hj j hjN
        exact ⟨c', hc', hc'f⟩

/-- In a sink component, an element pushed somewhere visits every point. -/
theorem visits (hω1 : ∀ e ∈ M.E, 1 ≤ ω e) {η : α → ZMod D}
    (hsink : ∀ ψ, Reach M ω η ψ → Reach M ω ψ η) {ψ₁ : α → ZMod D} (h₁ : Reach M ω η ψ₁)
    {f : α} (hf : f ∈ M.E) (hp : Pushable M ψ₁ ω f) (x : ZMod D) :
    ∃ ψ, Reach M ω η ψ ∧ f ∈ arcSet M ψ ω x := by
  have h₂ : Reach M ω η (push ψ₁ f) := h₁.tail ⟨f, hf, hp, rfl⟩
  have hback : Reach M ω (push ψ₁ f) ψ₁ := (hsink _ h₂).trans h₁
  obtain ⟨N, hN, hj⟩ := reach_values f hback
  rw [push_apply_self] at hN
  have hN' : (N : ZMod D) = -1 := by
    rw [hN]
    ring
  have hND : D - 1 ≤ N := by
    have h := congrArg ZMod.val hN'
    rw [ZMod.val_natCast, val_neg_one'] at h
    have := Nat.mod_le N D
    omega
  obtain ⟨c, hc, hcf⟩ := hj (x - push ψ₁ f f).val
    (by have := ZMod.val_lt (x - push ψ₁ f f); omega)
  have hcx : c f = x := by
    rw [hcf, ZMod.natCast_zmod_val]
    ring
  refine ⟨c, h₂.trans hc, hf, ?_⟩
  rw [hcx, sub_self, ZMod.val_zero]
  exact hω1 f hf

end HigherRankKUM.VHT
