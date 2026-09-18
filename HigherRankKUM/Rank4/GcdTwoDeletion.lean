import HigherRankKUM.StrictDensity
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Combinatorics.Matroid.Minor.Delete

namespace HigherRankKUM
namespace Rank4GcdTwoDeletion

open Set
open scoped Matroid

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
    (hH : DangerousHyperplane M k H) (hE : M.E.Finite) :
    H.Finite :=
  hE.subset hH.subset_ground

theorem DangerousHyperplane.ncard_eq
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hH : DangerousHyperplane M k H) (hE : M.E.Finite) :
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
  have hjleNat : j ≤ 3 := by
    exact_mod_cast hjle
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


/-- A single-element deletion of a strict rank-four `4k+2` instance
fails the `(4k+1)/4` density inequality exactly when the deleted element is
avoided by a dangerous hyperplane.

This is the formal obstruction characterization behind the good-deletion
count: the only possible failure after deletion is a rank-three set of
cardinality `3k+1`, and strict density forces such a set to be a flat. -/
theorem not_uniformlyDenseRatio_delete_iff_exists_dangerous
    {M : Matroid α} {k : ℕ} {e : α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (he : e ∈ M.E) :
    (¬ UniformlyDenseRatio (M ＼ ({e} : Set α)) (4 * k + 1) 4) ↔
      ∃ H : Set α, DangerousHyperplane M k H ∧ e ∉ H := by
  constructor
  · intro hbad
    rw [UniformlyDenseRatio] at hbad
    push_neg at hbad
    obtain ⟨X, hXdel, hfail⟩ := hbad
    have hXsub : X ⊆ M.E \ ({e} : Set α) := by
      simpa [Matroid.delete_ground] using hXdel
    have hXE : X ⊆ M.E :=
      hXsub.trans Set.sdiff_subset
    have heX : e ∉ X := by
      intro heMem
      exact (hXsub heMem).2 (by simp)
    have hXfin : X.Finite := hE.subset hXE
    have hRkDelete :
        (M ＼ ({e} : Set α)).eRk X = M.eRk X := by
      simpa [Matroid.delete_eq_restrict] using
        M.restrict_eRk_eq hXsub
    rw [hRkDelete, ← hXfin.cast_ncard_eq] at hfail
    have hRk4 : M.eRk X ≤ (4 : ℕ∞) := by
      rw [← hRank]
      exact M.eRk_le_eRank X
    obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRk4
    have hjleNat : j ≤ 4 := by
      exact_mod_cast hjle
    have hXne : X ≠ ∅ := by
      intro hzero
      subst X
      simp at hfail
    have hXnonempty : X.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hXne
    have hXproper : X ≠ M.E := by
      intro hEq
      have : e ∈ X := by
        rw [hEq]
        exact he
      exact heX this
    have hs := hStrict X hXE hXnonempty hXproper
    rw [← hXfin.cast_ncard_eq, hj] at hs
    rw [hj] at hfail
    have hfailNat : (4 * k + 1) * j < 4 * X.ncard := by
      exact_mod_cast hfail
    have hsNat : 4 * X.ncard < (4 * k + 2) * j := by
      exact_mod_cast hs
    have hj3 : j = 3 := by
      interval_cases j <;> omega
    subst j
    have hXcard : X.ncard = 3 * k + 1 := by
      norm_num at hfailNat hsNat
      omega
    have hXrank : M.eRk X = (3 : ℕ∞) := by
      simpa using hj
    have hXflat : M.IsFlat X := by
      rw [Matroid.isFlat_iff_closure_eq]
      apply Set.Subset.antisymm
      · have hclSub : M.closure X ⊆ M.E :=
          M.closure_subset_ground X
        have hclFin : (M.closure X).Finite :=
          hE.subset hclSub
        by_contra hnotSub
        have hneClosure : X ≠ M.closure X := by
          intro hEq
          apply hnotSub
          rw [← hEq]
        have hss : X ⊂ M.closure X :=
          (M.subset_closure X hXE).ssubset_of_ne hneClosure
        have hcardLt : X.ncard < (M.closure X).ncard :=
          Set.ncard_lt_ncard hss hclFin
        have hclNonempty : (M.closure X).Nonempty :=
          hXnonempty.mono (M.subset_closure X hXE)
        have hclProper : M.closure X ≠ M.E := by
          intro hEq
          have hr := M.eRk_closure_eq X
          rw [hEq, M.eRk_ground, hRank, hXrank] at hr
          norm_num at hr
        have hscl := hStrict (M.closure X) hclSub hclNonempty hclProper
        rw [← hclFin.cast_ncard_eq, M.eRk_closure_eq, hXrank] at hscl
        have hsclNat :
            4 * (M.closure X).ncard < (4 * k + 2) * 3 := by
          exact_mod_cast hscl
        omega
      · exact M.subset_closure X hXE
    have hXencard : X.encard = ((3 * k + 1 : ℕ) : ℕ∞) := by
      rw [← hXfin.cast_ncard_eq, hXcard]
    exact ⟨X, ⟨hXflat, hXrank, hXencard⟩, heX⟩
  · rintro ⟨H, hH, heH⟩ hDenseDelete
    have hHdel : H ⊆ (M ＼ ({e} : Set α)).E := by
      rw [Matroid.delete_ground]
      intro x hx
      refine ⟨hH.subset_ground hx, ?_⟩
      simpa only [Set.mem_singleton_iff] using
        (fun hxe : x = e => heH (hxe ▸ hx))
    have hdense := hDenseDelete H hHdel
    have hRkDelete :
        (M ＼ ({e} : Set α)).eRk H = M.eRk H := by
      have hHsub : H ⊆ M.E \ ({e} : Set α) := by
        simpa [Matroid.delete_ground] using hHdel
      simpa [Matroid.delete_eq_restrict] using
        M.restrict_eRk_eq hHsub
    rw [hRkDelete, hH.2.1, hH.2.2] at hdense
    have hdenseNat :
        4 * (3 * k + 1) ≤ (4 * k + 1) * 3 := by
      exact_mod_cast hdense
    omega

/-- The finite family of dangerous hyperplanes in a fixed rank-four
`4k+2` instance. -/
def dangerousHyperplanes (M : Matroid α) (k : ℕ) : Set (Set α) :=
  {H | DangerousHyperplane M k H}

@[simp] theorem mem_dangerousHyperplanes
    {M : Matroid α} {k : ℕ} {H : Set α} :
    H ∈ dangerousHyperplanes M k ↔ DangerousHyperplane M k H :=
  Iff.rfl

theorem dangerousHyperplanes_finite
    {M : Matroid α} {k : ℕ}
    (hE : M.E.Finite) :
    (dangerousHyperplanes M k).Finite := by
  apply hE.finite_subsets.subset
  intro H hH
  exact hH.subset_ground

/-- There are at most three dangerous hyperplanes in a strict rank-four
`4k+2` instance. Four of their pairwise disjoint `(k+1)`-element
complements would already require `4k+4` ground elements. -/
theorem dangerousHyperplanes_ncard_le_three
    {M : Matroid α} {k : ℕ}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4) :
    (dangerousHyperplanes M k).ncard ≤ 3 := by
  have hDfin : (dangerousHyperplanes M k).Finite :=
    dangerousHyperplanes_finite hE
  by_contra hle
  have hgt : 3 < (dangerousHyperplanes M k).ncard := by omega
  obtain ⟨H₀, H₁, H₂, H₃,
      hH₀mem, hH₁mem, hH₂mem, hH₃mem,
      h01, h02, h03, h12, h13, h23⟩ :=
    (Set.three_lt_ncard_iff hDfin).1 hgt
  have hH₀ : DangerousHyperplane M k H₀ := hH₀mem
  have hH₁ : DangerousHyperplane M k H₁ := hH₁mem
  have hH₂ : DangerousHyperplane M k H₂ := hH₂mem
  have hH₃ : DangerousHyperplane M k H₃ := hH₃mem
  let C₀ := M.E \ H₀
  let C₁ := M.E \ H₁
  let C₂ := M.E \ H₂
  let C₃ := M.E \ H₃
  have hC₀fin : C₀.Finite := hE.sdiff
  have hC₁fin : C₁.Finite := hE.sdiff
  have hC₂fin : C₂.Finite := hE.sdiff
  have hC₃fin : C₃.Finite := hE.sdiff
  have hC₀card : C₀.ncard = k + 1 := by
    simpa [C₀] using dangerous_complement_ncard_eq hE hEcard hH₀
  have hC₁card : C₁.ncard = k + 1 := by
    simpa [C₁] using dangerous_complement_ncard_eq hE hEcard hH₁
  have hC₂card : C₂.ncard = k + 1 := by
    simpa [C₂] using dangerous_complement_ncard_eq hE hEcard hH₂
  have hC₃card : C₃.ncard = k + 1 := by
    simpa [C₃] using dangerous_complement_ncard_eq hE hEcard hH₃
  have hd01 : Disjoint C₀ C₁ := by
    simpa [C₀, C₁] using
      dangerous_complements_disjoint hE hRank hEcard hStrict hH₀ hH₁ h01
  have hd02 : Disjoint C₀ C₂ := by
    simpa [C₀, C₂] using
      dangerous_complements_disjoint hE hRank hEcard hStrict hH₀ hH₂ h02
  have hd03 : Disjoint C₀ C₃ := by
    simpa [C₀, C₃] using
      dangerous_complements_disjoint hE hRank hEcard hStrict hH₀ hH₃ h03
  have hd12 : Disjoint C₁ C₂ := by
    simpa [C₁, C₂] using
      dangerous_complements_disjoint hE hRank hEcard hStrict hH₁ hH₂ h12
  have hd13 : Disjoint C₁ C₃ := by
    simpa [C₁, C₃] using
      dangerous_complements_disjoint hE hRank hEcard hStrict hH₁ hH₃ h13
  have hd23 : Disjoint C₂ C₃ := by
    simpa [C₂, C₃] using
      dangerous_complements_disjoint hE hRank hEcard hStrict hH₂ hH₃ h23
  have hd012 : Disjoint (C₀ ∪ C₁) C₂ := by
    rw [Set.disjoint_left]
    intro x hx hx2
    rcases hx with hx0 | hx1
    · exact (Set.disjoint_left.1 hd02) hx0 hx2
    · exact (Set.disjoint_left.1 hd12) hx1 hx2
  have hd0123 : Disjoint ((C₀ ∪ C₁) ∪ C₂) C₃ := by
    rw [Set.disjoint_left]
    intro x hx hx3
    rcases hx with hx01 | hx2
    · rcases hx01 with hx0 | hx1
      · exact (Set.disjoint_left.1 hd03) hx0 hx3
      · exact (Set.disjoint_left.1 hd13) hx1 hx3
    · exact (Set.disjoint_left.1 hd23) hx2 hx3
  have hC01card : (C₀ ∪ C₁).ncard = 2 * (k + 1) := by
    rw [Set.ncard_union_eq hd01 hC₀fin hC₁fin, hC₀card, hC₁card]
    omega
  have hC012card : ((C₀ ∪ C₁) ∪ C₂).ncard = 3 * (k + 1) := by
    rw [Set.ncard_union_eq hd012 (hC₀fin.union hC₁fin) hC₂fin,
      hC01card, hC₂card]
    omega
  have hC0123card : (((C₀ ∪ C₁) ∪ C₂) ∪ C₃).ncard = 4 * (k + 1) := by
    rw [Set.ncard_union_eq hd0123
      ((hC₀fin.union hC₁fin).union hC₂fin) hC₃fin,
      hC012card, hC₃card]
    omega
  have hAllSub : ((C₀ ∪ C₁) ∪ C₂) ∪ C₃ ⊆ M.E := by
    dsimp [C₀, C₁, C₂, C₃]
    exact Set.union_subset
      (Set.union_subset
        (Set.union_subset Set.sdiff_subset Set.sdiff_subset)
        Set.sdiff_subset)
      Set.sdiff_subset
  have hUpper :
      (((C₀ ∪ C₁) ∪ C₂) ∪ C₃).ncard ≤ M.E.ncard :=
    Set.ncard_le_ncard hAllSub hE
  have hEn : M.E.ncard = 4 * k + 2 := by
    have h := hEcard
    rw [← hE.cast_ncard_eq] at h
    exact_mod_cast h
  rw [hC0123card, hEn] at hUpper
  omega


/-- Ground elements whose deletion fails the `(4k+1)/4` density inequality. -/
def badDeletionElements (M : Matroid α) (k : ℕ) : Set α :=
  {e | e ∈ M.E ∧
    ¬ UniformlyDenseRatio (M ＼ ({e} : Set α)) (4 * k + 1) 4}

/-- Ground elements whose deletion preserves the `(4k+1)/4` density
inequality. -/
def goodDeletionElements (M : Matroid α) (k : ℕ) : Set α :=
  {e | e ∈ M.E ∧
    UniformlyDenseRatio (M ＼ ({e} : Set α)) (4 * k + 1) 4}

/-- The bad deletion elements are exactly the union of the dangerous
hyperplane complements. -/
theorem badDeletionElements_eq_biUnion_dangerous
    {M : Matroid α} {k : ℕ}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4) :
    badDeletionElements M k =
      ⋃ H ∈ dangerousHyperplanes M k, M.E \ H := by
  ext e
  constructor
  · rintro ⟨heE, hbad⟩
    obtain ⟨H, hH, heH⟩ :=
      (not_uniformlyDenseRatio_delete_iff_exists_dangerous
        hE hRank hStrict heE).1 hbad
    exact Set.mem_iUnion.2 ⟨H,
      Set.mem_iUnion.2 ⟨hH, ⟨heE, heH⟩⟩⟩
  · intro heUnion
    obtain ⟨H, heUnion⟩ := Set.mem_iUnion.1 heUnion
    obtain ⟨hH, heComp⟩ := Set.mem_iUnion.1 heUnion
    refine ⟨heComp.1, ?_⟩
    exact
      (not_uniformlyDenseRatio_delete_iff_exists_dangerous
        hE hRank hStrict heComp.1).2 ⟨H, hH, heComp.2⟩

/-- The number of bad deletion elements is exactly
`t(k+1)`, where `t` is the number of dangerous hyperplanes. -/
theorem badDeletionElements_ncard_eq
    {M : Matroid α} {k : ℕ}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4) :
    (badDeletionElements M k).ncard =
      (dangerousHyperplanes M k).ncard * (k + 1) := by
  rw [badDeletionElements_eq_biUnion_dangerous hE hRank hStrict]
  have hDfin : (dangerousHyperplanes M k).Finite :=
    dangerousHyperplanes_finite hE
  have hCompFin :
      ∀ H ∈ dangerousHyperplanes M k, (M.E \ H).Finite := by
    intro H hH
    exact hE.sdiff
  have hPair :
      (dangerousHyperplanes M k).PairwiseDisjoint
        (fun H => M.E \ H) := by
    intro H hH K hK hne
    exact dangerous_complements_disjoint
      hE hRank hEcard hStrict hH hK hne
  rw [hDfin.ncard_biUnion hCompFin hPair]
  calc
    (∑ᶠ H ∈ dangerousHyperplanes M k, (M.E \ H).ncard)
        = ∑ᶠ H ∈ dangerousHyperplanes M k, 1 * (k + 1) := by
            apply finsum_mem_congr rfl
            intro H hH
            rw [dangerous_complement_ncard_eq hE hEcard hH]
            simp
    _ = (∑ᶠ H ∈ dangerousHyperplanes M k, 1) * (k + 1) := by
          rw [finsum_mem_mul]
    _ = (dangerousHyperplanes M k).ncard * (k + 1) := by
          rw [finsum_one]

/-- Good deletion elements are the ground-set complement of the bad ones. -/
theorem goodDeletionElements_eq_sdiff_bad
    (M : Matroid α) (k : ℕ) :
    goodDeletionElements M k = M.E \ badDeletionElements M k := by
  classical
  ext e
  simp [goodDeletionElements, badDeletionElements]

/-- Exact good-deletion count in the strict rank-four `4k+2` case. -/
theorem goodDeletionElements_ncard_eq
    {M : Matroid α} {k : ℕ}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4) :
    (goodDeletionElements M k).ncard =
      (4 * k + 2) -
        (dangerousHyperplanes M k).ncard * (k + 1) := by
  rw [goodDeletionElements_eq_sdiff_bad]
  have hBadSub : badDeletionElements M k ⊆ M.E := by
    intro e he
    exact he.1
  have hEn : M.E.ncard = 4 * k + 2 := by
    have h := hEcard
    rw [← hE.cast_ncard_eq] at h
    exact_mod_cast h
  rw [Set.ncard_sdiff' hBadSub hE, hEn,
    badDeletionElements_ncard_eq hE hRank hEcard hStrict]

/-- Quantitative deletion theorem: at least `k-1` ground elements have a
uniformly dense deletion. The bound is sharp in the binary family recorded in
the research ledger. -/
theorem goodDeletionElements_ncard_ge_k_sub_one
    {M : Matroid α} {k : ℕ}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4) :
    k - 1 ≤ (goodDeletionElements M k).ncard := by
  rw [goodDeletionElements_ncard_eq hE hRank hEcard hStrict]
  have ht :
      (dangerousHyperplanes M k).ncard ≤ 3 :=
    dangerousHyperplanes_ncard_le_three hE hRank hEcard hStrict
  have hmul :
      (dangerousHyperplanes M k).ncard * (k + 1) ≤
        3 * (k + 1) :=
    Nat.mul_le_mul_right (k + 1) ht
  have hmono :=
    Nat.sub_le_sub_left hmul (4 * k + 2)
  have hcalc : (4 * k + 2) - 3 * (k + 1) = k - 1 := by
    omega
  rw [hcalc] at hmono
  exact hmono

/-- For `k ≥ 2`, a strict rank-four matroid on `4k+2` elements has at
least one deletion preserving uniform density at the new ratio
`(4k+1)/4`. -/
theorem exists_good_deletion_of_two_le
    {M : Matroid α} {k : ℕ}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hk : 2 ≤ k) :
    ∃ e ∈ M.E,
      UniformlyDenseRatio (M ＼ ({e} : Set α)) (4 * k + 1) 4 := by
  have hGoodFin : (goodDeletionElements M k).Finite := by
    apply hE.subset
    intro e he
    exact he.1
  have hlower :=
    goodDeletionElements_ncard_ge_k_sub_one hE hRank hEcard hStrict
  have hpos : 0 < (goodDeletionElements M k).ncard := by
    omega
  obtain ⟨e, heGood⟩ :=
    (Set.ncard_pos hGoodFin).1 hpos
  exact ⟨e, heGood.1, heGood.2⟩

end

end Rank4GcdTwoDeletion
end HigherRankKUM
