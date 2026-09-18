import HigherRankKUM.StrictDensity
import Mathlib.Data.Set.Card

namespace HigherRankKUM
namespace Rank4GcdTwoDeletion

open Set

noncomputable section

variable {α : Type*}

/-- A rank-three flat of the extremal size `3k+1` in a rank-four
`4k+2` strict-density instance. Such flats are exactly the geometric
obstructions that can make a single deletion fail uniform density. -/
def DangerousHyperplane (M : Matroid α) (k : ℕ) (H : Set α) : Prop :=
  M.IsFlat H ∧
    M.eRk H = (3 : ℕ∞) ∧
    H.encard = ((3 * k + 1 : ℕ) : ℕ∞)

theorem DangerousHyperplane.subset_ground
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hH : DangerousHyperplane M k H) :
    H ⊆ M.E :=
  hH.1.subset_ground

theorem DangerousHyperplane.finite
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hE : M.E.Finite) (hH : DangerousHyperplane M k H) :
    H.Finite :=
  hE.subset hH.subset_ground

theorem DangerousHyperplane.ncard_eq
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hE : M.E.Finite) (hH : DangerousHyperplane M k H) :
    H.ncard = 3 * k + 1 := by
  have hHfin := hH.finite hE
  have hcard := hH.2.2
  rw [← hHfin.cast_ncard_eq] at hcard
  exact_mod_cast hcard

/-- A dangerous rank-three flat is proper when the ambient matroid has rank
four. -/
theorem DangerousHyperplane.ne_ground
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hH : DangerousHyperplane M k H) :
    H ≠ M.E := by
  intro hEq
  have hr := hH.2.1
  rw [hEq, M.eRk_ground, hRank] at hr
  norm_num at hr

/-- Binary intersections of flats are flats. This small local lemma keeps the
dangerous-hyperplane argument independent of any bundled flat lattice API. -/
theorem isFlat_inter_of_isFlat
    {M : Matroid α} {H K : Set α}
    (hH : M.IsFlat H) (hK : M.IsFlat K) :
    M.IsFlat (H ∩ K) := by
  rw [Matroid.isFlat_iff_closure_eq]
  apply Set.Subset.antisymm
  · exact Set.subset_inter
      ((M.closure_subset_closure Set.inter_subset_left).trans_eq hH.closure)
      ((M.closure_subset_closure Set.inter_subset_right).trans_eq hK.closure)
  · exact M.subset_closure (H ∩ K)
      (Set.inter_subset_left.trans hH.subset_ground)

/-- Distinct dangerous hyperplanes have intersection of rank at most two.
The proof uses only flatness, equal finite cardinality, and rank three; density
enters later only to convert this rank bound into the sharp `2k` size bound. -/
theorem dangerous_inter_eRk_le_two
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hE : M.E.Finite)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K) :
    M.eRk (H ∩ K) ≤ (2 : ℕ∞) := by
  have hHfin := hH.finite hE
  have hIfin : (H ∩ K).Finite :=
    hHfin.subset Set.inter_subset_left
  have hIflat : M.IsFlat (H ∩ K) :=
    isFlat_inter_of_isFlat hH.1 hK.1
  have hIneH : H ∩ K ≠ H := by
    intro hEq
    have hHK : H ⊆ K := by
      intro x hxH
      have hxI : x ∈ H ∩ K := by
        rw [hEq]
        exact hxH
      exact hxI.2
    have hHK_eq : H = K :=
      hHfin.eq_of_subset_of_encard_le hHK (by
        rw [hH.2.2, hK.2.2])
    exact hne hHK_eq
  have hle3 : M.eRk (H ∩ K) ≤ (3 : ℕ∞) := by
    calc
      M.eRk (H ∩ K) ≤ M.eRk H :=
        M.eRk_mono Set.inter_subset_left
      _ = (3 : ℕ∞) := hH.2.1
  have hne3 : M.eRk (H ∩ K) ≠ (3 : ℕ∞) := by
    intro hr3
    have hge : M.eRk H ≤ M.eRk (H ∩ K) := by
      rw [hH.2.1, hr3]
    have hclos :=
      (M.isRkFinite_of_finite hIfin).closure_eq_closure_of_subset_of_eRk_ge_eRk
        Set.inter_subset_left hge
    have hset : H ∩ K = H := by
      rw [hIflat.closure, hH.1.closure] at hclos
      exact hclos
    exact hIneH hset
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hle3
  have hjne : j ≠ 3 := by
    intro hj3
    subst j
    exact hne3 (by simpa using hj)
  have hjle2 : j ≤ 2 := by omega
  rw [hj]
  exact_mod_cast hjle2

/-- Strict `(4k+2)/4` density gives the sharp capacity bound `|X| ≤ 2k`
for every ground-set subset of rank at most two. -/
theorem ncard_le_two_mul_of_strict_of_eRk_le_two
    {M : Matroid α} {k : ℕ} {X : Set α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hX : X ⊆ M.E)
    (hRk : M.eRk X ≤ (2 : ℕ∞)) :
    X.ncard ≤ 2 * k := by
  by_cases hXempty : X = ∅
  · simp [hXempty]
  have hXnonempty : X.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hXempty
  have hXproper : X ≠ M.E := by
    intro hEq
    have hr := hRk
    rw [hEq, M.eRk_ground, hRank] at hr
    norm_num at hr
  have hXfin : X.Finite := hE.subset hX
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRk
  have hs := hStrict X hX hXnonempty hXproper
  rw [← hXfin.cast_ncard_eq, hj] at hs
  have hsNat : 4 * X.ncard < (4 * k + 2) * j := by
    exact_mod_cast hs
  have hmul : (4 * k + 2) * j ≤ (4 * k + 2) * 2 :=
    Nat.mul_le_mul_left (4 * k + 2) hjle
  have hlt : 4 * X.ncard < (4 * k + 2) * 2 :=
    hsNat.trans_le hmul
  omega

/-- If every rank-at-most-two set has size at most `2k`, then two distinct
dangerous hyperplanes cover the whole ground set. -/
theorem dangerous_union_eq_ground_of_rankTwoCap
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hE : M.E.Finite)
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K)
    (hCap : ∀ X : Set α, X ⊆ M.E →
      M.eRk X ≤ (2 : ℕ∞) → X.ncard ≤ 2 * k) :
    H ∪ K = M.E := by
  have hHfin := hH.finite hE
  have hKfin := hK.finite hE
  have hHn : H.ncard = 3 * k + 1 := hH.ncard_eq hE
  have hKn : K.ncard = 3 * k + 1 := hK.ncard_eq hE
  have hEn : M.E.ncard = 4 * k + 2 := by
    have h := hEcard
    rw [← hE.cast_ncard_eq] at h
    exact_mod_cast h
  have hIrank : M.eRk (H ∩ K) ≤ (2 : ℕ∞) :=
    dangerous_inter_eRk_le_two hE hH hK hne
  have hIcard : (H ∩ K).ncard ≤ 2 * k :=
    hCap (H ∩ K)
      (Set.inter_subset_left.trans hH.subset_ground) hIrank
  have hcount :=
    Set.ncard_union_add_ncard_inter H K hHfin hKfin
  have hUnionLower : 4 * k + 2 ≤ (H ∪ K).ncard := by
    rw [hHn, hKn] at hcount
    omega
  have hUnionSub : H ∪ K ⊆ M.E :=
    Set.union_subset hH.subset_ground hK.subset_ground
  have hUnionUpper : (H ∪ K).ncard ≤ M.E.ncard :=
    Set.ncard_le_ncard hUnionSub hE
  have hUnionCard : (H ∪ K).ncard = M.E.ncard := by
    rw [hEn] at hUnionUpper ⊢
    omega
  exact Set.eq_of_subset_of_ncard_le hUnionSub hUnionCard.ge hE

/-- Under the same capacity hypothesis, distinct dangerous hyperplanes meet
in exactly `2k` elements. -/
theorem dangerous_inter_ncard_eq_two_mul_of_rankTwoCap
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hE : M.E.Finite)
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K)
    (hCap : ∀ X : Set α, X ⊆ M.E →
      M.eRk X ≤ (2 : ℕ∞) → X.ncard ≤ 2 * k) :
    (H ∩ K).ncard = 2 * k := by
  have hHfin := hH.finite hE
  have hKfin := hK.finite hE
  have hHn : H.ncard = 3 * k + 1 := hH.ncard_eq hE
  have hKn : K.ncard = 3 * k + 1 := hK.ncard_eq hE
  have hEn : M.E.ncard = 4 * k + 2 := by
    have h := hEcard
    rw [← hE.cast_ncard_eq] at h
    exact_mod_cast h
  have hUnion :=
    dangerous_union_eq_ground_of_rankTwoCap
      hE hEcard hH hK hne hCap
  have hcount :=
    Set.ncard_union_add_ncard_inter H K hHfin hKfin
  rw [hUnion, hEn, hHn, hKn] at hcount
  omega

/-- The central dangerous-hyperplane geometry: distinct extremal rank-three
flats have pairwise disjoint complements. -/
theorem dangerous_complements_disjoint_of_rankTwoCap
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hE : M.E.Finite)
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K)
    (hCap : ∀ X : Set α, X ⊆ M.E →
      M.eRk X ≤ (2 : ℕ∞) → X.ncard ≤ 2 * k) :
    Disjoint (M.E \ H) (M.E \ K) := by
  have hUnion :=
    dangerous_union_eq_ground_of_rankTwoCap
      hE hEcard hH hK hne hCap
  rw [Set.disjoint_left]
  intro x hxH hxK
  have hxUnion : x ∈ H ∪ K := by
    rw [hUnion]
    exact hxH.1
  rcases hxUnion with hx | hx
  · exact hxH.2 hx
  · exact hxK.2 hx

/-- Each dangerous hyperplane has a complement of exactly `k+1` elements. -/
theorem dangerous_complement_ncard_eq
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hE : M.E.Finite)
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hH : DangerousHyperplane M k H) :
    (M.E \ H).ncard = k + 1 := by
  have hHn : H.ncard = 3 * k + 1 := hH.ncard_eq hE
  have hEn : M.E.ncard = 4 * k + 2 := by
    have h := hEcard
    rw [← hE.cast_ncard_eq] at h
    exact_mod_cast h
  rw [Set.ncard_sdiff' hH.subset_ground hE, hEn, hHn]
  omega

/-- In a strict rank-four `4k+2` instance, distinct dangerous hyperplanes
have disjoint `(k+1)`-element complements. This is the formal version of the
key counting lemma from the density-slack deletion argument. -/
theorem dangerous_complements_disjoint
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K) :
    Disjoint (M.E \ H) (M.E \ K) := by
  apply dangerous_complements_disjoint_of_rankTwoCap
    hE hEcard hH hK hne
  intro X hX hRk
  exact ncard_le_two_mul_of_strict_of_eRk_le_two
    hE hRank hStrict hX hRk

/-- Strict density also forces the exact `2k` intersection size of two
distinct dangerous hyperplanes. -/
theorem dangerous_inter_ncard_eq_two_mul
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K) :
    (H ∩ K).ncard = 2 * k := by
  apply dangerous_inter_ncard_eq_two_mul_of_rankTwoCap
    hE hEcard hH hK hne
  intro X hX hRk
  exact ncard_le_two_mul_of_strict_of_eRk_le_two
    hE hRank hStrict hX hRk

end

end Rank4GcdTwoDeletion
end HigherRankKUM
