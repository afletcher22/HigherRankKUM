import Probe.VHT.Reach

/-!
# Theorem 2.1, steps 5–6: the claims and the core case

Fix a sink state `η`, and let `U` be the unbounded elements: those pushed somewhere in its
component.

* A bounded element `e` never moves. The closure of the other elements at its first point `η e`
  is the same everywhere in the component, and it contains `U`. Since `e` is never pushable,
  `e` is not in the closure of `(E(η e) ∪ U) \ {e}` (`claim3`).
* For every point `x` and every independent `J ⊆ U`, the set `(E_η(x) \ U) ∪ J` is independent
  (`indep_union`). This is the paper's Claim 5 combined with the contraction step, stated
  without contraction matroids.
* `U` is not the whole ground set, provided some point set of `η` is dependent
  (`unbounded_ne_ground`).
* The core case of Theorem 2.1 (every weight between `1` and `D - 1`) follows by applying the
  induction hypothesis to `M ↾ U` (`core`).
-/

namespace HigherRankKUM.VHT

open Set

variable {α : Type*} [DecidableEq α] {M : Matroid α} {D : ℕ} [NeZero D] {ω : α → ℕ}

/-- The elements pushed somewhere in the component of `η`. -/
def unbounded (M : Matroid α) (ω : α → ℕ) (η : α → ZMod D) : Set α :=
  {e | e ∈ M.E ∧ ∃ ψ, Reach M ω η ψ ∧ Pushable M ψ ω e}

theorem unbounded_subset (η : α → ZMod D) : unbounded M ω η ⊆ M.E := fun _ h => h.1

/-- A bounded element never moves. -/
theorem bounded_fixed {η ψ : α → ZMod D} (h : Reach M ω η ψ) {e : α}
    (he : e ∉ unbounded M ω η) : ψ e = η e := by
  induction h with
  | refl => rfl
  | @tail b c hab hbc ih =>
    obtain ⟨g, hg, hp, rfl⟩ := hbc
    have hge : e ≠ g := by
      rintro rfl
      exact he ⟨hg, b, hab, hp⟩
    rw [push_apply_ne _ hge, ih]

/-- Every ground-set element covers its own first point. -/
theorem mem_arcSet_self (hω1 : ∀ e ∈ M.E, 1 ≤ ω e) (φ : α → ZMod D) {e : α} (he : e ∈ M.E) :
    e ∈ arcSet M φ ω (φ e) := by
  refine ⟨he, ?_⟩
  rw [sub_self, ZMod.val_zero]
  exact hω1 e he

/-- One push inside the component does not shrink the closure of the other elements at a bounded
element's first point. -/
theorem closure_diff_mono_step (hω1 : ∀ e ∈ M.E, 1 ≤ ω e) (hω : ∀ e ∈ M.E, ω e < D)
    {η χ χ' : α → ZMod D} (hχ : Reach M ω η χ) {e : α} (heE : e ∈ M.E)
    (he : e ∉ unbounded M ω η) (hstep : PushStep M ω χ χ') :
    M.closure (arcSet M χ ω (η e) \ {e}) ⊆ M.closure (arcSet M χ' ω (η e) \ {e}) := by
  obtain ⟨g, hg, hp, rfl⟩ := hstep
  have hge : e ≠ g := by
    rintro rfl
    exact he ⟨hg, χ, hχ, hp⟩
  have hχe : χ e = η e := bounded_fixed hχ he
  by_cases hx : η e = χ g
  · rw [hx, arcSet_push_self hω]
    set E0 := arcSet M χ ω (χ g) with hE0
    have heE0 : e ∈ E0 := by
      have h := mem_arcSet_self hω1 χ heE
      rwa [hχe, hx] at h
    have hgE0 : g ∈ E0 := mem_arcSet_self hω1 χ hg
    have hnp : e ∉ M.closure (E0 \ {e}) := by
      intro h
      apply he
      refine ⟨heE, χ, hχ, ?_⟩
      show e ∈ M.closure (arcSet M χ ω (χ e) \ {e})
      rw [hχe, hx]
      exact h
    set X := E0 \ {g} \ {e} with hX
    have h1 : E0 \ {g} = insert e X := by
      ext a
      simp only [hX, mem_diff, mem_singleton_iff, mem_insert_iff]
      constructor
      · rintro ⟨ha, hag⟩
        by_cases hae : a = e
        · exact Or.inl hae
        · exact Or.inr ⟨⟨ha, hag⟩, hae⟩
      · rintro (rfl | ⟨⟨ha, hag⟩, -⟩)
        · exact ⟨heE0, hge⟩
        · exact ⟨ha, hag⟩
    have h2 : E0 \ {e} = insert g X := by
      ext a
      simp only [hX, mem_diff, mem_singleton_iff, mem_insert_iff]
      constructor
      · rintro ⟨ha, hae⟩
        by_cases hag : a = g
        · exact Or.inl hag
        · exact Or.inr ⟨⟨ha, hag⟩, hae⟩
      · rintro (rfl | ⟨⟨ha, -⟩, hae⟩)
        · exact ⟨hgE0, fun h => hge h.symm⟩
        · exact ⟨ha, hae⟩
    have hgX : g ∈ M.closure X := by
      by_contra hgX
      have hp' : g ∈ M.closure (insert e X) := by
        rw [← h1]
        exact hp
      have hex := Matroid.closure_exchange ⟨hp', hgX⟩
      apply hnp
      rw [h2]
      exact hex.1
    rw [h2, Matroid.closure_insert_eq_of_mem_closure hgX]
  · exact M.closure_subset_closure (diff_subset_diff_left (arcSet_subset_push χ g hx))

theorem closure_diff_mono (hω1 : ∀ e ∈ M.E, 1 ≤ ω e) (hω : ∀ e ∈ M.E, ω e < D)
    {η a b : α → ZMod D} (ha : Reach M ω η a) (hab : Reach M ω a b) {e : α} (heE : e ∈ M.E)
    (he : e ∉ unbounded M ω η) :
    M.closure (arcSet M a ω (η e) \ {e}) ⊆ M.closure (arcSet M b ω (η e) \ {e}) := by
  induction hab with
  | refl => exact subset_rfl
  | @tail b c hab' hbc ih =>
    exact ih.trans (closure_diff_mono_step hω1 hω (ha.trans hab') heE he hbc)

/-- **Claim 3.** A bounded element is not spanned by the other elements at its first point
together with the unbounded elements. -/
theorem claim3 (hω1 : ∀ e ∈ M.E, 1 ≤ ω e) (hω : ∀ e ∈ M.E, ω e < D) {η : α → ZMod D}
    (hsink : ∀ ψ, Reach M ω η ψ → Reach M ω ψ η) {e : α} (heE : e ∈ M.E)
    (he : e ∉ unbounded M ω η) {ψ : α → ZMod D} (hψ : Reach M ω η ψ) :
    e ∉ M.closure ((arcSet M ψ ω (η e) ∪ unbounded M ω η) \ {e}) := by
  have hcl : ∀ ψ', Reach M ω η ψ' →
      M.closure (arcSet M ψ' ω (η e) \ {e}) = M.closure (arcSet M η ω (η e) \ {e}) := by
    intro ψ' hψ'
    exact (closure_diff_mono hω1 hω hψ' (hsink ψ' hψ') heE he).antisymm
      (closure_diff_mono hω1 hω Relation.ReflTransGen.refl hψ' heE he)
  have hU : unbounded M ω η ⊆ M.closure (arcSet M ψ ω (η e) \ {e}) := by
    rintro f ⟨hfE, ψ₁, h₁, hp⟩
    obtain ⟨ψ', hψ', hfx⟩ := visits hω1 hsink h₁ hfE hp (η e)
    have hfe : f ≠ e := by
      rintro rfl
      exact he ⟨hfE, ψ₁, h₁, hp⟩
    have hmem : f ∈ M.closure (arcSet M ψ' ω (η e) \ {e}) :=
      M.subset_closure _ (diff_subset.trans (arcSet_subset M ψ' ω _)) ⟨hfx, hfe⟩
    rwa [hcl ψ' hψ', ← hcl ψ hψ] at hmem
  have hnot : e ∉ M.closure (arcSet M ψ ω (η e) \ {e}) := by
    intro h
    apply he
    refine ⟨heE, ψ, hψ, ?_⟩
    show e ∈ M.closure (arcSet M ψ ω (ψ e) \ {e})
    rw [bounded_fixed hψ he]
    exact h
  intro h
  apply hnot
  refine M.closure_subset_closure_of_subset_closure ?_ h
  rintro a ⟨ha | ha, hae⟩
  · exact M.subset_closure _ (diff_subset.trans (arcSet_subset M ψ ω _)) ⟨ha, hae⟩
  · exact hU ha

/-- **Claim 5, with the combination step.** For every point `x` and every independent set `J` of
unbounded elements, the bounded part of `E_η(x)` together with `J` is independent. -/
theorem indep_union (hω1 : ∀ e ∈ M.E, 1 ≤ ω e) (hω : ∀ e ∈ M.E, ω e < D) {η : α → ZMod D}
    (hsink : ∀ ψ, Reach M ω η ψ → Reach M ω ψ η) (x : ZMod D) {J : Set α} (hJ : M.Indep J)
    (hJU : J ⊆ unbounded M ω η) :
    M.Indep ((arcSet M η ω x \ unbounded M ω η) ∪ J) := by
  by_contra hdep
  have hsubE : (arcSet M η ω x \ unbounded M ω η) ∪ J ⊆ M.E :=
    union_subset (diff_subset.trans (arcSet_subset M η ω x)) hJ.subset_ground
  obtain ⟨C, hCX, hC⟩ := ((Matroid.not_indep_iff hsubE).1 hdep).exists_isCircuit_subset
  set CB := C \ unbounded M ω η with hCB
  have hCBx : CB ⊆ arcSet M η ω x := by
    rintro a ⟨haC, haU⟩
    rcases hCX haC with ha | ha
    · exact ha.1
    · exact absurd (hJU ha) haU
  rcases CB.eq_empty_or_nonempty with hempty | hne
  · apply hC.not_indep
    refine hJ.subset fun a haC => ?_
    rcases hCX haC with ha | ha
    · exact absurd (show a ∈ CB from ⟨haC, ha.2⟩) (by rw [hempty]; exact not_mem_empty a)
    · exact ha
  obtain ⟨e, ⟨heC, heU⟩, hstart⟩ := exists_start hω η hne hCBx
  have heE : e ∈ M.E := hC.subset_ground heC
  apply claim3 hω1 hω hsink heE heU Relation.ReflTransGen.refl
  refine M.closure_subset_closure ?_ (hC.mem_closure_sdiff_singleton_of_mem heC)
  rintro a ⟨haC, hae⟩
  refine ⟨?_, hae⟩
  by_cases haU : a ∈ unbounded M ω η
  · exact Or.inr haU
  · exact Or.inl (hstart ⟨haC, haU⟩)

/-- If some point set of `η` is dependent, the unbounded elements are not the whole ground set. -/
theorem unbounded_ne_ground (hE : M.E.Finite) (hω1 : ∀ e ∈ M.E, 1 ≤ ω e)
    (hω : ∀ e ∈ M.E, ω e < D) (hW : WeightBounded M ω D) {η : α → ZMod D} (hbη : IsBest M η ω)
    (hsink : ∀ ψ, Reach M ω η ψ → Reach M ω ψ η) (hdep : ∃ x, ¬ M.Indep (arcSet M η ω x)) :
    unbounded M ω η ≠ M.E := by
  intro hUE
  obtain ⟨x₀, hx₀⟩ := hdep
  have hspan : ∀ x, M.eRk (arcSet M η ω x) = M.eRank := by
    intro x
    have hsub : M.E ⊆ M.closure (arcSet M η ω x) := by
      intro f hf
      rw [← hUE] at hf
      obtain ⟨hfE, ψ₁, h₁, hp⟩ := hf
      obtain ⟨ψ', hψ', hfx⟩ := visits hω1 hsink h₁ hfE hp x
      have h := M.mem_closure_of_mem hfx (arcSet_subset M ψ' ω x)
      rwa [(reach_isBest hE hω hbη hψ').2 x] at h
    rw [← M.eRk_closure_eq, (M.closure_subset_ground _).antisymm hsub, M.eRk_ground]
  have hrfin : M.eRank ≠ ⊤ := by
    have h := M.eRk_le_encard M.E
    rw [M.eRk_ground] at h
    exact ne_top_of_le_ne_top hE.encard_lt_top.ne h
  set r := M.eRank.toNat with hr
  have hrc : (r : ℕ∞) = M.eRank := ENat.coe_toNat hrfin
  have hfin : ∀ x, (arcSet M η ω x).Finite := fun x => hE.subset (arcSet_subset M η ω x)
  have hge : ∀ x ∈ (Finset.univ : Finset (ZMod D)), r ≤ (arcSet M η ω x).ncard := by
    intro x _
    have h := M.eRk_le_encard (arcSet M η ω x)
    rw [hspan x, ← hrc, ← (hfin x).cast_ncard_eq] at h
    exact_mod_cast h
  have hsum : ∑ x : ZMod D, (arcSet M η ω x).ncard ≤ ∑ _x : ZMod D, r := by
    rw [sum_ncard_arcSet hE (fun e he => (hω e he).le) η, Finset.sum_const, Finset.card_univ,
      ZMod.card, smul_eq_mul]
    have h := hW hE.toFinset (by simp)
    rw [Set.Finite.coe_toFinset, M.eRk_ground, ← hrc] at h
    exact_mod_cast h
  have heq := (Finset.sum_eq_sum_iff_of_le hge).1 (le_antisymm (Finset.sum_le_sum hge) hsum)
  apply hx₀
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite (hfin x₀), hspan x₀, ← hrc,
    ← (hfin x₀).cast_ncard_eq, ← heq x₀ (Finset.mem_univ _)]

/-- **The core case of Theorem 2.1**: all weights lie between `1` and `D - 1`, given the result for
matroids on smaller ground sets. -/
theorem core (hE : M.E.Finite) (hL : M.Loopless) (hW : WeightBounded M ω D)
    (hω1 : ∀ e ∈ M.E, 1 ≤ ω e) (hω : ∀ e ∈ M.E, ω e < D)
    (ih : ∀ N : Matroid α, N.E ⊂ M.E → N.Loopless → WeightBounded N ω D →
      ∃ φ : α → ZMod D, ∀ x, N.Indep (arcSet N φ ω x)) :
    ∃ φ : α → ZMod D, ∀ x, M.Indep (arcSet M φ ω x) := by
  classical
  obtain ⟨φ₀, hb₀⟩ := exists_isBest (D := D) hE ω
  obtain ⟨η, hη, hsink⟩ := exists_sink (ω := ω) hE φ₀
  have hbη := (reach_isBest hE hω hb₀ hη).1
  by_cases hsol : ∀ x, M.Indep (arcSet M η ω x)
  · exact ⟨η, hsol⟩
  push_neg at hsol
  set U := unbounded M ω η with hU
  have hUss : U ⊂ M.E :=
    (unbounded_subset η).ssubset_of_ne (unbounded_ne_ground hE hω1 hω hW hbη hsink hsol)
  have hLU : (M ↾ U).Loopless := by
    rw [Matroid.loopless_iff_forall_not_isLoop]
    intro e heU hloop
    rw [Matroid.restrict_isLoop_iff] at hloop
    rcases hloop.2 with h | h
    · exact (Matroid.loopless_iff_forall_not_isLoop.1 hL) e (hUss.subset heU) h
    · exact h (hUss.subset heU)
  have hWU : WeightBounded (M ↾ U) ω D := by
    intro A hA
    rw [Matroid.restrict_eRk_eq _ hA]
    exact hW A (hA.trans hUss.subset)
  obtain ⟨φU, hφU⟩ := ih (M ↾ U) hUss hLU hWU
  refine ⟨fun a => if a ∈ U then φU a else η a, fun x => ?_⟩
  have hsplit : arcSet M (fun a => if a ∈ U then φU a else η a) ω x =
      (arcSet M η ω x \ U) ∪ arcSet (M ↾ U) φU ω x := by
    ext a
    by_cases ha : a ∈ U
    · simp [arcSet, ha, hUss.subset ha]
    · simp [arcSet, ha]
  rw [hsplit]
  exact indep_union hω1 hω hsink x (hφU x).of_restrict (arcSet_subset (M ↾ U) φU ω x)

end HigherRankKUM.VHT
