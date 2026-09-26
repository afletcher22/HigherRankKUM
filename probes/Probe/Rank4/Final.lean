import Probe.Rank4.Full
import Probe.Rank4.LemmaH
import Probe.Rank4.LemmaU
import Probe.EncHBridgeG
import Probe.Hit14Line
import Probe.Hit14G
import HigherRankKUM.VHT.Covers

/-!
# Rank-4 KUM

The hitting lemma (`HittingLemma`) comes from:

* for `k ≥ 4`, Lemma U applied to a double cover from van den Heuvel–Thomassé;
* for `k = 3`, one of three cases:
  * a 9-element plane: the `hit14g` certificate;
  * a 6-element line and no 9-element plane: the `hit14line` certificate;
  * neither: Lemma H.

Together with `solvesKUMAtRank_four_of_hitting`, it gives rank-4 KUM.
-/

namespace HigherRankKUM

open Set Probe.Enc
open scoped Matroid

/-- The hitting lemma at `k = 3`. -/
theorem hitting_three {α : Type*} (M : Matroid α) (hT : Hitting.StrictT0 M 3) :
    ∃ S, Hitting.Deletable M 3 S := by
  by_cases h9 : ∃ K, M.IsFlat K ∧ M.eRk K = 3 ∧ K.encard = ((3 * 3 : ℕ) : ℕ∞)
  · obtain ⟨K, hKflat, hKrank, hKcard⟩ := h9
    exact deletable_of_hitG Hit14G.no_model hT hKflat.subset_ground hKrank hKcard
  push_neg at h9
  by_cases h6 : ∃ L, M.IsFlat L ∧ M.eRk L = 2 ∧ L.encard = ((2 * 3 : ℕ) : ℕ∞)
  · obtain ⟨L, hLflat, hLrank, hLcard⟩ := h6
    exact deletable_of_hitLine Hit14Line.no_model hT hLflat.subset_ground hLrank hLcard h9
  push_neg at h6
  obtain ⟨S, hS, hD⟩ := Hitting.lemmaH M 3 (by norm_num) hT h9 h6
  exact ⟨S, Hitting.deletable_of_meetsDemands hT (by norm_num) hS hD⟩

/-- The hitting lemma for `k ≥ 4`: Lemma U applied to a double cover. -/
theorem hitting_ge_four {α : Type*} (M : Matroid α) {k : ℕ} (hk : 4 ≤ k)
    (hT : Hitting.StrictT0 M k) : ∃ S, Hitting.Deletable M k S := by
  have hDense : UniformlyDenseRatio M (4 * k + 2) 4 := by
    intro X hX
    rcases X.eq_empty_or_nonempty with rfl | hne
    · simp
    by_cases hXE : X = M.E
    · rw [hXE, M.eRk_ground, hT.rank, hT.card]
      exact le_of_eq (by push_cast; ring)
    · exact le_of_lt (hT.strict X hX hne hXE)
  obtain ⟨φ, hφ⟩ := VHT.double_cover VHT.theorem_2_1 M (k := k) (by omega) hT.finite hT.card
    (hT.rank.trans (by norm_num)) hDense
  haveI : NeZero (2 * k + 1) := ⟨by omega⟩
  haveI : Fact (1 < 2 * k + 1) := ⟨by omega⟩
  let ψ := ZMod.finEquiv (2 * k + 1)
  let B : Fin (2 * k + 1) → Set α := fun i => arcSet M φ (fun _ => 2) (ψ i)
  have hB : ∀ i, M.IsBase (B i) := fun i => hφ (ψ i)
  have hcover : ∀ e ∈ M.E, ∃ i j, i ≠ j ∧ e ∈ B i ∧ e ∈ B j ∧
      ∀ l, e ∈ B l → l = i ∨ l = j := by
    intro e he
    have hmem : ∀ l, e ∈ B l ↔ ψ l = φ e ∨ ψ l = φ e + 1 := by
      intro l
      show e ∈ M.E ∧ (ψ l - φ e).val < 2 ↔ _
      constructor
      · rintro ⟨-, hl⟩
        have hv : (ψ l - φ e).val = 0 ∨ (ψ l - φ e).val = 1 := by omega
        rcases hv with hv | hv
        · exact Or.inl (sub_eq_zero.1 ((ZMod.val_eq_zero _).1 hv))
        · right
          have h1 : ψ l - φ e = 1 := ZMod.val_injective _ (hv.trans (ZMod.val_one _).symm)
          rw [← h1]
          ring
      · rintro (h | h)
        · refine ⟨he, ?_⟩
          rw [h, sub_self, ZMod.val_zero]
          norm_num
        · refine ⟨he, ?_⟩
          rw [h, add_sub_cancel_left, ZMod.val_one]
          norm_num
    refine ⟨ψ.symm (φ e), ψ.symm (φ e + 1), ?_, (hmem _).2 (Or.inl ?_),
      (hmem _).2 (Or.inr ?_), ?_⟩
    · intro h
      have h' := congrArg ψ h
      simp only [RingEquiv.apply_symm_apply] at h'
      have h1 : (1 : ZMod (2 * k + 1)) = 0 := by simpa using h'
      exact one_ne_zero h1
    · exact ψ.apply_symm_apply _
    · exact ψ.apply_symm_apply _
    · intro l hl
      rcases (hmem l).1 hl with h | h
      · left
        rw [← h, RingEquiv.symm_apply_apply]
      · right
        rw [← h, RingEquiv.symm_apply_apply]
  obtain ⟨i, hi⟩ := Hitting.lemmaU M k hk hT B hB hcover
  exact ⟨B i, Hitting.deletable_of_meetsDemands hT (by omega) (hB i) hi⟩

/-- **The hitting lemma** for every `k ≥ 3`. -/
theorem hittingLemma {α : Type*} : HittingLemma α := by
  intro M k hk hT
  rcases Nat.lt_or_ge k 4 with h | h
  · have hk3 : k = 3 := by omega
    subst hk3
    exact hitting_three M hT
  · exact hitting_ge_four M h hT

/-- **Rank-4 KUM**: every uniformly dense rank-4 matroid has a cyclic basis ordering. -/
theorem solvesKUMAtRank_four {α : Type*} : SolvesKUMAtRank α 4 :=
  solvesKUMAtRank_four_of_hitting hittingLemma

#print axioms solvesKUMAtRank_four

end HigherRankKUM
