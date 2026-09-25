import HigherRankKUM.StrictDensity
import HigherRankKUM.RationalDensity
import HigherRankKUM.Rank4.GcdTwoDeletion

/-!
# The hitting lemma: shared definitions and the deletability criterion

`StrictT0 M k`: `M` is a strict rank-4 matroid on `4k+2` elements with no dangerous hyperplane.
Then every set of rank `1`, `2` or `3` has at most `k`, `2k` or `3k` elements
(`StrictT0.ncard_le`).

A basis `S` is *deletable* if `M \ S` is uniformly dense at ratio `(4k-2)/4`. The *demand flats*
are the `k`-points, the `2k`-lines, the `3k`-planes and the `(3k-1)`-planes. `S` *meets the
demands* if it meets each of these, and each `3k`-plane at least twice. A basis that meets the
demands is deletable (`deletable_of_meetsDemands`).

Lemma H (no `3k`-plane and no `2k`-line, `k ≥ 2`) and Lemma U (every double cover, `k ≥ 4`)
produce bases that meet the demands. Their statements are `LemmaHStatement` and
`LemmaUStatement`.
-/

namespace HigherRankKUM
namespace Hitting

open Set
open scoped Matroid

variable {α : Type*} {M : Matroid α} {k : ℕ}

/-- A strict rank-4 matroid on `4k+2` elements with no dangerous hyperplane. -/
structure StrictT0 (M : Matroid α) (k : ℕ) : Prop where
  finite : M.E.Finite
  rank : M.eRank = (4 : ℕ∞)
  card : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞)
  strict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4
  noDanger : ∀ H, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H

/-- A basis whose complement is uniformly dense at ratio `(4k-2)/4`. -/
def Deletable (M : Matroid α) (k : ℕ) (S : Set α) : Prop :=
  M.IsBase S ∧ UniformlyDenseRatio (M ↾ (M.E \ S)) (4 * k - 2) 4

/-- `S` meets every demand flat, and every `3k`-plane at least twice. -/
def MeetsDemands (M : Matroid α) (k : ℕ) (S : Set α) : Prop :=
  (∀ F, M.IsFlat F → M.eRk F = 1 → F.encard = (k : ℕ∞) → (F ∩ S).Nonempty) ∧
  (∀ F, M.IsFlat F → M.eRk F = 2 → F.encard = ((2 * k : ℕ) : ℕ∞) → (F ∩ S).Nonempty) ∧
  (∀ F, M.IsFlat F → M.eRk F = 3 → F.encard = ((3 * k : ℕ) : ℕ∞) → 2 ≤ (F ∩ S).encard) ∧
  (∀ F, M.IsFlat F → M.eRk F = 3 → F.encard = ((3 * k - 1 : ℕ) : ℕ∞) → (F ∩ S).Nonempty)

namespace StrictT0

theorem exists_eRk_eq (h : StrictT0 M k) (X : Set α) : ∃ j : ℕ, M.eRk X = j ∧ j ≤ 4 := by
  have hle : M.eRk X ≤ (4 : ℕ∞) := by
    rw [← h.rank]
    exact M.eRk_le_eRank X
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hle
  exact ⟨j, hj, by exact_mod_cast hjle⟩

theorem ncard_ground (h : StrictT0 M k) : M.E.ncard = 4 * k + 2 := by
  have h' := h.card
  rw [← h.finite.cast_ncard_eq] at h'
  exact_mod_cast h'

/-- Strict density for a nonempty set of rank at most `3`. -/
theorem four_mul_ncard_lt (h : StrictT0 M k) {X : Set α} (hX : X ⊆ M.E) (hne : X.Nonempty)
    {j : ℕ} (hj : M.eRk X = j) (hj3 : j ≤ 3) : 4 * X.ncard < (4 * k + 2) * j := by
  have hXfin : X.Finite := h.finite.subset hX
  have hproper : X ≠ M.E := by
    intro hEq
    rw [hEq, M.eRk_ground, h.rank] at hj
    have h4 : (4 : ℕ) = j := by exact_mod_cast hj
    omega
  have hs := h.strict X hX hne hproper
  rw [← hXfin.cast_ncard_eq, hj] at hs
  exact_mod_cast hs

/-- **The strict t=0 profile.** A set of rank `j ≤ 3` has at most `j k` elements. -/
theorem ncard_le (h : StrictT0 M k) {X : Set α} (hX : X ⊆ M.E) {j : ℕ} (hj : M.eRk X = j)
    (hj3 : j ≤ 3) : X.ncard ≤ j * k := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · simp
  have hlt := h.four_mul_ncard_lt hX hne hj hj3
  by_cases hj3' : j = 3
  · subst hj3'
    -- `|X| ≤ 3k+1`, and `3k+1` would make `cl X` a dangerous hyperplane
    by_contra hbig
    have hXcard : X.ncard = 3 * k + 1 := by omega
    have hclE : M.closure X ⊆ M.E := M.closure_subset_ground X
    have hclfin : (M.closure X).Finite := h.finite.subset hclE
    have hclrk : M.eRk (M.closure X) = ((3 : ℕ) : ℕ∞) := by rw [M.eRk_closure_eq, hj]
    have hcllt := h.four_mul_ncard_lt hclE (hne.mono (M.subset_closure X hX)) hclrk le_rfl
    have hle : X.ncard ≤ (M.closure X).ncard :=
      Set.ncard_le_ncard (M.subset_closure X hX) hclfin
    have hclcard : (M.closure X).ncard = 3 * k + 1 := by omega
    apply h.noDanger (M.closure X)
    refine ⟨M.isFlat_closure X, ?_, ?_⟩
    · rw [M.eRk_closure_eq]
      exact_mod_cast hj
    · rw [← hclfin.cast_ncard_eq, hclcard]
  · interval_cases j <;> omega

end StrictT0

/-- **Deletability.** Under the strict t=0 profile, a basis that meets the demands is deletable. -/
theorem deletable_of_meetsDemands (h : StrictT0 M k) (hk : 1 ≤ k) {S : Set α}
    (hS : M.IsBase S) (hD : MeetsDemands M k S) : Deletable M k S := by
  obtain ⟨hD1, hD2, hD3, hD3'⟩ := hD
  have hSE : S ⊆ M.E := hS.subset_ground
  have hSfin : S.Finite := h.finite.subset hSE
  have hScard : S.ncard = 4 := by
    have h4 : S.encard = (4 : ℕ∞) := by rw [hS.encard_eq_eRank, h.rank]
    rw [← hSfin.cast_ncard_eq] at h4
    exact_mod_cast h4
  have hdiff : (M.E \ S).ncard + S.ncard = M.E.ncard := by
    have h' : (M.E \ S).encard + S.encard = M.E.encard :=
      Set.encard_sdiff_add_encard_of_subset hSE
    rw [← (h.finite.subset diff_subset).cast_ncard_eq, ← hSfin.cast_ncard_eq,
      ← h.finite.cast_ncard_eq] at h'
    exact_mod_cast h'
  have hEcard := h.ncard_ground
  refine ⟨hS, fun X hX => ?_⟩
  have hXS : X ⊆ M.E \ S := hX
  have hXE : X ⊆ M.E := hXS.trans diff_subset
  have hXfin : X.Finite := h.finite.subset hXE
  rw [Matroid.restrict_eRk_eq M hXS]
  obtain ⟨j, hj, hj4⟩ := h.exists_eRk_eq X
  rw [← hXfin.cast_ncard_eq, hj]
  suffices hN : 4 * X.ncard ≤ (4 * k - 2) * j by exact_mod_cast hN
  -- the closure of `X`, which avoids `S` on `X`
  obtain ⟨F, hFdef⟩ : ∃ F, F = M.closure X := ⟨_, rfl⟩
  have hFE : F ⊆ M.E := hFdef ▸ M.closure_subset_ground X
  have hFfin : F.Finite := h.finite.subset hFE
  have hXF : X ⊆ F := hFdef ▸ M.subset_closure X hXE
  have hFrk : M.eRk F = j := by rw [hFdef, M.eRk_closure_eq, hj]
  have hFflat : M.IsFlat F := hFdef ▸ M.isFlat_closure X
  have hFSfin : (F ∩ S).Finite := hFfin.subset inter_subset_left
  have hsplit : X.ncard + (F ∩ S).ncard ≤ F.ncard := by
    have hdisj : Disjoint X (F ∩ S) := by
      rw [Set.disjoint_left]
      intro x hxX hxFS
      exact (hXS hxX).2 hxFS.2
    rw [← Set.ncard_union_eq hdisj hXfin hFSfin]
    exact Set.ncard_le_ncard (union_subset hXF inter_subset_left) hFfin
  have hFenc : F.encard = (F.ncard : ℕ∞) := hFfin.cast_ncard_eq.symm
  have hmeet : (F ∩ S).Nonempty → 1 ≤ (F ∩ S).ncard := fun hne =>
    (Set.ncard_pos hFSfin).2 hne
  interval_cases j
  · have := h.ncard_le hXE hj (by norm_num)
    omega
  · have hFle := h.ncard_le hFE hFrk (by norm_num)
    by_cases hFk : F.ncard = k
    · have := hmeet (hD1 F hFflat (by exact_mod_cast hFrk) (by rw [hFenc, hFk]))
      omega
    · omega
  · have hFle := h.ncard_le hFE hFrk (by norm_num)
    by_cases hFk : F.ncard = 2 * k
    · have := hmeet (hD2 F hFflat (by exact_mod_cast hFrk) (by rw [hFenc, hFk]))
      omega
    · omega
  · have hFle := h.ncard_le hFE hFrk (by norm_num)
    by_cases hFk : F.ncard = 3 * k
    · have h2 := hD3 F hFflat (by exact_mod_cast hFrk) (by rw [hFenc, hFk])
      rw [← hFSfin.cast_ncard_eq] at h2
      have h2' : 2 ≤ (F ∩ S).ncard := by exact_mod_cast h2
      omega
    · by_cases hFk' : F.ncard = 3 * k - 1
      · have := hmeet (hD3' F hFflat (by exact_mod_cast hFrk) (by rw [hFenc, hFk']))
        omega
      · omega
  · have := Set.ncard_le_ncard hXS (h.finite.subset diff_subset)
    omega

/-- **Lemma H** (hitting lemma, reduced case): with no `3k`-plane and no `2k`-line, some basis
meets the demands. -/
def LemmaHStatement (α : Type*) : Prop :=
  ∀ (M : Matroid α) (k : ℕ), 2 ≤ k → StrictT0 M k →
    (∀ F, M.IsFlat F → M.eRk F = 3 → F.encard ≠ ((3 * k : ℕ) : ℕ∞)) →
    (∀ F, M.IsFlat F → M.eRk F = 2 → F.encard ≠ ((2 * k : ℕ) : ℕ∞)) →
    ∃ S, M.IsBase S ∧ MeetsDemands M k S

/-- **Lemma U** (unified hitting lemma): for `k ≥ 4`, some basis of every double cover meets
the demands. A double cover is a family of `2k+1` bases in which every element lies in exactly
two. -/
def LemmaUStatement (α : Type*) : Prop :=
  ∀ (M : Matroid α) (k : ℕ), 4 ≤ k → StrictT0 M k →
    ∀ B : Fin (2 * k + 1) → Set α, (∀ i, M.IsBase (B i)) →
    (∀ e ∈ M.E, ∃ i j, i ≠ j ∧ e ∈ B i ∧ e ∈ B j ∧ ∀ l, e ∈ B l → l = i ∨ l = j) →
    ∃ i, MeetsDemands M k (B i)

end Hitting
end HigherRankKUM
