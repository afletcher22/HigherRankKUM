import HigherRankKUM.VHT.Push

/-!
# Theorem 2.1, step 1: best mappings

The potential of `φ` is the total size of the closures of its point sets. A *best* mapping
maximizes it; one exists because the potential depends only on the finitely many values of `φ`
on the ground set. Pushing a pushable element never shrinks a closure (`closure_push`). So a push
applied to a best mapping keeps every closure unchanged and gives another best mapping.

Also: with every weight at most `D`, the point sets have total size `Σ_e ω e`.
-/

namespace HigherRankKUM.VHT

open Set

variable {α : Type*} [DecidableEq α] {M : Matroid α} {D : ℕ} [NeZero D] {ω : α → ℕ}

/-- Total size of the closures of all point sets. -/
noncomputable def potential (M : Matroid α) (φ : α → ZMod D) (ω : α → ℕ) : ℕ :=
  ∑ x : ZMod D, (M.closure (arcSet M φ ω x)).ncard

/-- `φ` maximizes the potential. -/
def IsBest (M : Matroid α) (φ : α → ZMod D) (ω : α → ℕ) : Prop :=
  ∀ ψ : α → ZMod D, potential M ψ ω ≤ potential M φ ω

theorem arcSet_congr {φ ψ : α → ZMod D} (h : ∀ e ∈ M.E, φ e = ψ e) (x : ZMod D) :
    arcSet M φ ω x = arcSet M ψ ω x := by
  ext e
  simp only [arcSet, mem_setOf_eq]
  constructor
  · rintro ⟨he, hx⟩
    exact ⟨he, by rwa [← h e he]⟩
  · rintro ⟨he, hx⟩
    exact ⟨he, by rwa [h e he]⟩

theorem potential_congr {φ ψ : α → ZMod D} (h : ∀ e ∈ M.E, φ e = ψ e) :
    potential M φ ω = potential M ψ ω := by
  unfold potential
  exact Finset.sum_congr rfl fun x _ => by rw [arcSet_congr h x]

open Classical in
/-- Extend a mapping on the ground set by `d` outside it. -/
noncomputable def extendGround (M : Matroid α) (g : M.E → ZMod D) (d : α → ZMod D) :
    α → ZMod D :=
  fun a => if h : a ∈ M.E then g ⟨a, h⟩ else d a

open Classical in
theorem extendGround_apply {g : M.E → ZMod D} {d : α → ZMod D} {a : α} (ha : a ∈ M.E) :
    extendGround M g d a = g ⟨a, ha⟩ :=
  dif_pos ha

open Classical in
theorem extendGround_apply_not_mem {g : M.E → ZMod D} {d : α → ZMod D} {a : α} (ha : a ∉ M.E) :
    extendGround M g d a = d a :=
  dif_neg ha

/-- A best mapping exists. -/
theorem exists_isBest (hE : M.E.Finite) (ω : α → ℕ) : ∃ φ : α → ZMod D, IsBest M φ ω := by
  haveI : Finite M.E := hE.to_subtype
  obtain ⟨g₀, hg₀⟩ :=
    Finite.exists_max fun g : M.E → ZMod D => potential M (extendGround M g fun _ => 0) ω
  refine ⟨extendGround M g₀ fun _ => 0, fun ψ => ?_⟩
  have h : potential M ψ ω = potential M (extendGround M (fun e : M.E => ψ e) fun _ => 0) ω :=
    potential_congr fun e he =>
      (extendGround_apply (g := fun e : M.E => ψ e) (d := fun _ => 0) he).symm
  rw [h]
  exact hg₀ fun e : M.E => ψ e

theorem closure_finite (hE : M.E.Finite) (φ : α → ZMod D) (x : ZMod D) :
    (M.closure (arcSet M φ ω x)).Finite :=
  hE.subset (M.closure_subset_ground _)

/-- Pushing a pushable element of a best mapping keeps every closure. -/
theorem push_closure_eq (hE : M.E.Finite) (hω : ∀ e ∈ M.E, ω e < D) {φ : α → ZMod D}
    (hb : IsBest M φ ω) {e : α} (hp : Pushable M φ ω e) (x : ZMod D) :
    M.closure (arcSet M (push φ e) ω x) = M.closure (arcSet M φ ω x) := by
  have hsub := closure_push hω φ hp
  have hle : ∀ y ∈ (Finset.univ : Finset (ZMod D)),
      (M.closure (arcSet M φ ω y)).ncard ≤ (M.closure (arcSet M (push φ e) ω y)).ncard :=
    fun y _ => Set.ncard_le_ncard (hsub y) (closure_finite hE _ y)
  have hsum : potential M φ ω = potential M (push φ e) ω :=
    le_antisymm (Finset.sum_le_sum hle) (hb _)
  have hx := (Finset.sum_eq_sum_iff_of_le hle).1 hsum x (Finset.mem_univ x)
  exact (Set.eq_of_subset_of_ncard_le (hsub x) hx.ge (closure_finite hE _ x)).symm

/-- A push of a best mapping is best. -/
theorem push_isBest (hE : M.E.Finite) (hω : ∀ e ∈ M.E, ω e < D) {φ : α → ZMod D}
    (hb : IsBest M φ ω) {e : α} (hp : Pushable M φ ω e) : IsBest M (push φ e) ω := by
  intro ψ
  have h : potential M (push φ e) ω = potential M φ ω := by
    unfold potential
    exact Finset.sum_congr rfl fun x _ => by rw [push_closure_eq hE hω hb hp x]
  rw [h]
  exact hb ψ

/-- With every weight at most `D`, the point sets have total size `Σ_e ω e`. -/
theorem sum_ncard_arcSet (hE : M.E.Finite) (hωD : ∀ e ∈ M.E, ω e ≤ D) (φ : α → ZMod D) :
    ∑ x : ZMod D, (arcSet M φ ω x).ncard = ∑ e ∈ hE.toFinset, ω e := by
  classical
  have harc : ∀ x, arcSet M φ ω x = ↑(hE.toFinset.filter fun e => (x - φ e).val < ω e) := by
    intro x
    ext e
    simp [arcSet]
  simp only [harc, Set.ncard_coe_finset, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.card_filter, card_arc, min_eq_left (hωD e (by simpa using he))]

end HigherRankKUM.VHT
