import Probe.Rank4.LemmaU
import HigherRankKUM.VHT.Covers
import HigherRankKUM.VHT.Theorem21

/-!
# The hitting lemma for `k ≥ 4`

Van den Heuvel–Thomassé give a double cover of a strict t=0 rank-4 matroid on `4k+2` elements:
`2k+1` bases, indexed by `ZMod (2k+1)`, in which every element lies in exactly two, namely the
arcs at `φ e` and `φ e + 1`. Reindexed by `Fin (2k+1)`, Lemma U finds a basis among them that
meets the demands, and so is deletable.
-/

namespace HigherRankKUM

open Set
open scoped Matroid

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
  let B : Fin (2 * k + 1) → Set α := fun i => VHT.arcSet M φ (fun _ => 2) (ψ i)
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

end HigherRankKUM
