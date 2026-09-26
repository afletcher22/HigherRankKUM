import Probe.EncHBridge
import HigherRankKUM.VHT.Covers
import HigherRankKUM.VHT.Theorem21

/-!
# The hitting lemma on 14 elements, 9-plane case

Let `M` be strict with `t = 0` on 14 elements (`k = 3`), with a plane `K` of 9 elements.

* By Edmonds (from van den Heuvel–Thomassé), `K` splits into three bases `D₀, D₁, D₂` of
  `M ↾ K`, since `M ↾ K` has rank 3 and at most `3 r(X)` elements in every set `X`.
* Number the ground set with `D₀, D₁, D₂` at positions `0–2`, `3–5`, `6–8`, and `E - K` at
  `9–13`.
* The certificate `hit14g` says that one of the 15 bases `Dᵢ + z` (`z ∉ K`) is deletable. This
  is the choice lemma of Theorem G at `k = 3` (`deletable_of_hitG`).
-/

namespace Probe.Enc

open Set HigherRankKUM
open scoped Matroid

variable {α : Type*}

theorem lowG14_le {M : Matroid α} (hT : Hitting.StrictT0 M 3) (pos : Fin 14 ≃ M.E) :
    ∀ X, X < 2 ^ 14 → lowG14.getD (pc 14 X) 0 ≤ maskRank M pos X := by
  intro X _
  have hYE : maskSet pos X ⊆ M.E := maskSet_subset pos X
  have hYfin : (maskSet pos X).Finite := hT.finite.subset hYE
  have hYcard : (maskSet pos X).ncard = pc 14 X := by
    have h := encard_maskSet pos X
    rw [← hYfin.cast_ncard_eq] at h
    exact_mod_cast h
  obtain ⟨j, hj, hj4⟩ := hT.exists_eRk_eq (maskSet pos X)
  rw [maskRank_eq pos hj, ← hYcard]
  have hpc : (maskSet pos X).ncard ≤ 14 := by
    rw [hYcard]
    unfold pc
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hle : j ≤ 3 → (maskSet pos X).ncard ≤ j * 3 := fun hj3 => hT.ncard_le hYE hj hj3
  have hlow : ∀ s ≤ 14, lowG14.getD s 0 =
      if s = 0 then 0 else if s ≤ 3 then 1 else if s ≤ 6 then 2 else if s ≤ 9 then 3 else 4 := by
    decide
  rw [hlow _ hpc]
  split_ifs <;> omega

/-- **The choice lemma of Theorem G at `k = 3`**, from its certificate: with a 9-element plane,
some basis is deletable. -/
theorem deletable_of_hitG
    (hcert : ∀ m : RankModelH 14 lowG14 (factsOfRanks [(511, 3), (7, 3), (56, 3), (448, 3)]),
      False)
    {M : Matroid α} (hT : Hitting.StrictT0 M 3) {K : Set α} (hKE : K ⊆ M.E)
    (hKrank : M.eRk K = 3) (hKcard : K.encard = ((9 : ℕ) : ℕ∞)) :
    ∃ S, Hitting.Deletable M 3 S := by
  by_contra hno
  push_neg at hno
  have hKfin : K.Finite := hT.finite.subset hKE
  -- an Edmonds partition of `K` into three bases of `M ↾ K`
  have hDenseK : UniformlyDenseRatio (M ↾ K) 3 1 := by
    intro X hX
    have hXK : X ⊆ K := hX
    have hXfin : X.Finite := hKfin.subset hXK
    rw [Matroid.restrict_eRk_eq M hXK]
    obtain ⟨j, hj, hj4⟩ := hT.exists_eRk_eq X
    have hj3 : j ≤ 3 := by
      have h := M.eRk_mono hXK
      rw [hj, hKrank] at h
      exact_mod_cast h
    have hle := hT.ncard_le (hXK.trans hKE) hj hj3
    rw [← hXfin.cast_ncard_eq, hj]
    have h1 : 1 * X.ncard ≤ 3 * j := by omega
    exact_mod_cast h1
  have hRankK : (M ↾ K).eRank = ((3 : ℕ) : ℕ∞) := by
    rw [← Matroid.eRk_ground, Matroid.restrict_ground_eq, Matroid.restrict_eRk_eq _ subset_rfl]
    exact hKrank.trans (by norm_num)
  obtain ⟨P, hPbase, hPpart⟩ := VHT.edmonds_partition VHT.theorem_2_1 (M ↾ K) (k := 3) (n := 9)
    (r := 3) (by norm_num) hKfin hKcard hRankK (by norm_num) hDenseK
  have hPK : ∀ x, P x ⊆ K := fun x => (hPbase x).subset_ground
  have hPcard : ∀ x, (P x).encard = ((3 : ℕ) : ℕ∞) := fun x =>
    (hPbase x).encard_eq_eRank.trans hRankK
  have hPrank : ∀ x, M.eRk (P x) = ((3 : ℕ) : ℕ∞) := by
    intro x
    have hI : M.Indep (P x) := (Matroid.restrict_indep_iff.1 (hPbase x).indep).1
    rw [hI.eRk_eq_encard, hPcard x]
  have hPdisj : ∀ x y, x ≠ y → ∀ e, e ∈ P x → e ∉ P y := by
    intro x y hxy e hx hy
    obtain ⟨z, -, hz⟩ := hPpart e (hPK x hx)
    exact hxy ((hz x hx).trans (hz y hy).symm)
  have hP2 : ∀ e, e ∈ P 2 ↔ e ∈ K ∧ e ∉ P 0 ∧ e ∉ P 1 := by
    intro e
    constructor
    · intro h
      exact ⟨hPK 2 h, hPdisj 2 0 (by decide) e h, hPdisj 2 1 (by decide) e h⟩
    · rintro ⟨hK, h0, h1⟩
      obtain ⟨x, hx, -⟩ := hPpart e hK
      fin_cases x
      · exact absurd hx h0
      · exact absurd hx h1
      · exact hx
  -- the numbering: `P 0`, `P 1`, `P 2`, then `E - K`
  have hP0K : P 0 ⊆ (M ↾ K).E := hPK 0
  have hK0card : (M ↾ K).E.encard = ((3 + 6 : ℕ) : ℕ∞) := hKcard.trans (by norm_num)
  have hR1card : (K \ P 0).encard = ((6 : ℕ) : ℕ∞) :=
    encard_diff_eq (M := M ↾ K) hKfin hP0K hK0card (hPcard 0)
  have hP1sub : P 1 ⊆ (M ↾ (K \ P 0)).E := fun e he =>
    ⟨hPK 1 he, hPdisj 1 0 (by decide) e he⟩
  have hR1card2 : (M ↾ (K \ P 0)).E.encard = ((3 + 3 : ℕ) : ℕ∞) := hR1card.trans (by norm_num)
  let e0 : Fin 3 ≃ P 0 := finEquivOfSetEncard (hKfin.subset (hPK 0)) (hPcard 0)
  let e1 : Fin 3 ≃ P 1 := finEquivOfSetEncard (hKfin.subset (hPK 1)) (hPcard 1)
  let e2 : Fin 3 ≃ ((M ↾ (K \ P 0)).E \ P 1 : Set α) :=
    finEquivOfSetEncard ((hKfin.subset diff_subset).subset diff_subset)
      (encard_diff_eq (M := M ↾ (K \ P 0)) (hKfin.subset diff_subset) hP1sub hR1card2
        (hPcard 1))
  let r1 : Fin 6 ≃ (M ↾ (K \ P 0)).E := blockEquiv hP1sub e1 e2
  let aK : Fin 9 ≃ (M ↾ K).E := blockEquiv hP0K e0 r1
  have hEcard : M.E.encard = ((9 + 5 : ℕ) : ℕ∞) := hT.card.trans (by norm_num)
  let cEnum : Fin 5 ≃ (M.E \ K : Set α) :=
    finEquivOfSetEncard (hT.finite.subset diff_subset) (encard_diff_eq hT.finite hKE hEcard hKcard)
  let pos : Fin 14 ≃ M.E := blockEquiv hKE aK cEnum
  -- where each position lies
  have hmK : ∀ p : Fin 14, (pos p : α) ∈ K ↔ (p : ℕ) < 9 := blockEquiv_mem_iff hKE aK cEnum
  have hval : ∀ (p : Fin 14) (h : (p : ℕ) < 9), (pos p : α) = aK ⟨p, h⟩ := fun p h =>
    blockEquiv_val_lt hKE aK cEnum p h
  have hm0 : ∀ q : Fin 9, (aK q : α) ∈ P 0 ↔ (q : ℕ) < 3 := blockEquiv_mem_iff hP0K e0 r1
  have hval1 : ∀ (q : Fin 9) (h : ¬ (q : ℕ) < 3), (aK q : α) = r1 ⟨q - 3, by omega⟩ :=
    fun q h => blockEquiv_val_ge hP0K e0 r1 q h
  have hm1 : ∀ t : Fin 6, (r1 t : α) ∈ P 1 ↔ (t : ℕ) < 3 := blockEquiv_mem_iff hP1sub e1 e2
  have hD0 : ∀ p : Fin 14, (pos p : α) ∈ P 0 ↔ (p : ℕ) < 3 := by
    intro p
    by_cases h : (p : ℕ) < 9
    · rw [hval p h, hm0]
    · exact iff_of_false (fun h0 => h ((hmK p).1 (hPK 0 h0))) (by omega)
  have hD1 : ∀ p : Fin 14, (pos p : α) ∈ P 1 ↔ 3 ≤ (p : ℕ) ∧ (p : ℕ) < 6 := by
    intro p
    by_cases h : (p : ℕ) < 9
    · rw [hval p h]
      by_cases h3 : (p : ℕ) < 3
      · have h0 : (aK ⟨p, h⟩ : α) ∈ P 0 := (hm0 ⟨p, h⟩).2 h3
        exact iff_of_false (hPdisj 0 1 (by decide) _ h0) (by omega)
      · rw [hval1 ⟨p, h⟩ h3, hm1]
        show (p : ℕ) - 3 < 3 ↔ _
        omega
    · exact iff_of_false (fun h1 => h ((hmK p).1 (hPK 1 h1))) (by omega)
  have hD2 : ∀ p : Fin 14, (pos p : α) ∈ P 2 ↔ 6 ≤ (p : ℕ) ∧ (p : ℕ) < 9 := by
    intro p
    rw [hP2, hmK, hD0, hD1]
    omega
  -- the named sets
  have hK : maskSet pos 511 = K := maskSet_eq pos hKE fun p => by
    rw [hmK p]
    revert p
    decide
  have hN0 : maskSet pos 7 = P 0 := maskSet_eq pos ((hPK 0).trans hKE) fun p => by
    rw [hD0 p]
    revert p
    decide
  have hN1 : maskSet pos 56 = P 1 := maskSet_eq pos ((hPK 1).trans hKE) fun p => by
    rw [hD1 p]
    revert p
    decide
  have hN2 : maskSet pos 448 = P 2 := maskSet_eq pos ((hPK 2).trans hKE) fun p => by
    rw [hD2 p]
    revert p
    decide
  have hranks : ∀ X s, (X, s) ∈ [((511 : ℕ), (3 : ℕ)), (7, 3), (56, 3), (448, 3)] →
      maskRank M pos X = s := by
    intro X s h
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · exact maskRank_eq pos (by rw [hK]; exact_mod_cast hKrank)
    · exact maskRank_eq pos (by rw [hN0]; exact hPrank 0)
    · exact maskRank_eq pos (by rw [hN1]; exact hPrank 1)
    · exact maskRank_eq pos (by rw [hN2]; exact hPrank 2)
    · simp at h
  exact hcert (rankModelH_of_pos hT pos (lowG14_le hT pos) (factT_of_ranks hranks)
    (factF_of_ranks hranks) hno)

end Probe.Enc
