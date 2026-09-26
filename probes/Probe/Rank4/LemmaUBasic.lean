import Probe.Rank4.Hitting

/-!
# Lemma U, part 1: counting infrastructure

General facts about a strict t=0 matroid (`StrictT0 M k`: rank 4, `4k+2` elements, no dangerous
hyperplane), used in the proof of Lemma U (`Probe.Rank4.LemmaU`).

* Sizes and ranks: a basis has 4 elements (`ncard_base`), an independent set has rank equal to
  its size (`eRk_indep`), and a basis meets a set of rank `r` in at most `r` elements
  (`ncard_inter_le`). There are no loops (`one_le_eRk`).
* Flats absorb spanning sets: if `I ⊆ G ∩ Y` with `G` a flat and `r(Y) ≤ r(I)`, then `Y ⊆ G`
  (`subset_flat`).
* Faces of a basis `B`: a plane meeting `B` in three elements is spanned by `B - b` for the one
  element `b ∈ B` it misses (`exists_mem_not_mem`, `sdiff_subset_of_three`, `plane_subset`).
* Pairwise disjoint subsets of the ground set have total size at most `4k+2` (`ncard_add3_le`,
  `ncard_add4_le`, `sum_ncard_le`).
* A basis that does not meet the demands misses some demand flat (`exists_viol`).
-/

namespace HigherRankKUM
namespace Hitting

open Set
open scoped Matroid

variable {α : Type*} {M : Matroid α} {k : ℕ}

namespace StrictT0

/-- A basis has four elements. -/
theorem ncard_base (h : StrictT0 M k) {B : Set α} (hB : M.IsBase B) : B.ncard = 4 := by
  have hBfin : B.Finite := h.finite.subset hB.subset_ground
  have h4 : B.encard = (4 : ℕ∞) := by rw [hB.encard_eq_eRank, h.rank]
  rw [← hBfin.cast_ncard_eq] at h4
  exact_mod_cast h4

/-- An independent set has rank equal to its size. -/
theorem eRk_indep (h : StrictT0 M k) {I : Set α} (hI : M.Indep I) :
    M.eRk I = (I.ncard : ℕ∞) := by
  rw [hI.eRk_eq_encard, (h.finite.subset hI.subset_ground).cast_ncard_eq]

/-- A basis meets a set of rank at most `r` in at most `r` elements. -/
theorem ncard_inter_le (h : StrictT0 M k) {B X : Set α} (hB : M.IsBase B) {r : ℕ}
    (hr : M.eRk X ≤ r) : (B ∩ X).ncard ≤ r := by
  have hI : M.Indep (B ∩ X) := hB.indep.subset inter_subset_left
  have h1 : ((B ∩ X).ncard : ℕ∞) ≤ r := by
    rw [← h.eRk_indep hI]
    exact (M.eRk_mono inter_subset_right).trans hr
  exact_mod_cast h1

/-- There are no loops: a nonempty set has positive rank. -/
theorem one_le_eRk (h : StrictT0 M k) {X : Set α} (hX : X ⊆ M.E) (hne : X.Nonempty) :
    1 ≤ M.eRk X := by
  obtain ⟨j, hj, -⟩ := h.exists_eRk_eq X
  have hpos := (Set.ncard_pos (h.finite.subset hX)).mpr hne
  rcases j with _ | j
  · have hle := h.ncard_le hX hj (by norm_num)
    omega
  · rw [hj]
    exact_mod_cast (by omega : 1 ≤ j + 1)

/-- **Flats absorb spanning sets.** If `I ⊆ G ∩ Y`, `G` is a flat and `r(Y) ≤ r(I)`, then
`Y ⊆ G`. -/
theorem subset_flat (h : StrictT0 M k) {G I Y : Set α} (hG : M.IsFlat G) (hIG : I ⊆ G)
    (hIY : I ⊆ Y) (hY : Y ⊆ M.E) (hr : M.eRk Y ≤ M.eRk I) : Y ⊆ G := by
  intro y hy
  by_contra hyG
  have hcl : M.closure I ⊆ G := (M.closure_subset_closure hIG).trans hG.closure.subset
  have hins : M.eRk (insert y I) = M.eRk I + 1 :=
    M.eRk_insert_eq_add_one ⟨hY hy, fun hmem => hyG (hcl hmem)⟩
  have hle : M.eRk (insert y I) ≤ M.eRk Y := M.eRk_mono (Set.insert_subset hy hIY)
  obtain ⟨j, hj, -⟩ := h.exists_eRk_eq I
  rw [hins, hj] at hle
  have hle2 := hle.trans hr
  rw [hj] at hle2
  have hfalse : j + 1 ≤ j := by exact_mod_cast hle2
  omega

/-- A basis is not contained in a set of rank at most `3`. -/
theorem exists_mem_not_mem (h : StrictT0 M k) {B G : Set α} (hB : M.IsBase B)
    (hG : M.eRk G ≤ (3 : ℕ)) : ∃ b ∈ B, b ∉ G := by
  by_contra hno
  push_neg at hno
  have h1 := h.ncard_inter_le hB hG
  rw [inter_eq_left.mpr hno, h.ncard_base hB] at h1
  omega

/-- A set meeting a basis `B` in at least three elements, and missing `b ∈ B`, contains
`B - b`. -/
theorem sdiff_subset_of_three (h : StrictT0 M k) {B G : Set α} (hB : M.IsBase B)
    (h3 : 3 ≤ (B ∩ G).ncard) {b : α} (hb : b ∈ B) (hbG : b ∉ G) : B \ {b} ⊆ G := by
  have hBfin : B.Finite := h.finite.subset hB.subset_ground
  have hsub : B ∩ G ⊆ B \ {b} := by
    rintro x ⟨hxB, hxG⟩
    refine ⟨hxB, fun hxb => hbG ?_⟩
    rw [Set.mem_singleton_iff] at hxb
    rw [← hxb]
    exact hxG
  have hcard : (B \ {b}).ncard = 3 := by
    have h1 := Set.ncard_sdiff_singleton_of_mem hb
    rw [h.ncard_base hB] at h1
    omega
  have heq : B ∩ G = B \ {b} :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (hBfin.subset Set.sdiff_subset)
  rw [← heq]
  exact inter_subset_right

/-- **Faces are determined by three basis elements.** If the flats `G` and `G2` both contain
`B - b`, and `G2` has rank at most `3`, then `G2 ⊆ G`. -/
theorem plane_subset (h : StrictT0 M k) {B G G2 : Set α} (hB : M.IsBase B) {b : α} (hb : b ∈ B)
    (hG : M.IsFlat G) (hG2 : M.IsFlat G2) (h3 : M.eRk G2 ≤ (3 : ℕ)) (hsub : B \ {b} ⊆ G)
    (hsub2 : B \ {b} ⊆ G2) : G2 ⊆ G := by
  have hcard : (B \ {b}).ncard = 3 := by
    have h1 := Set.ncard_sdiff_singleton_of_mem hb
    rw [h.ncard_base hB] at h1
    omega
  refine h.subset_flat hG hsub hsub2 hG2.subset_ground ?_
  rw [h.eRk_indep (hB.indep.subset Set.sdiff_subset), hcard]
  exact h3

/-- Three pairwise disjoint subsets of the ground set have total size at most `4k+2`. -/
theorem ncard_add3_le (h : StrictT0 M k) {X Y Z : Set α} (hX : X ⊆ M.E) (hY : Y ⊆ M.E)
    (hZ : Z ⊆ M.E) (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    X.ncard + Y.ncard + Z.ncard ≤ 4 * k + 2 := by
  have hf := h.finite
  rw [← Set.ncard_union_eq hXY (hf.subset hX) (hf.subset hY),
    ← Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hXZ, hYZ⟩)
      ((hf.subset hX).union (hf.subset hY)) (hf.subset hZ), ← h.ncard_ground]
  exact Set.ncard_le_ncard (union_subset (union_subset hX hY) hZ) hf

/-- Four pairwise disjoint subsets of the ground set have total size at most `4k+2`. -/
theorem ncard_add4_le (h : StrictT0 M k) {W X Y Z : Set α} (hW : W ⊆ M.E) (hX : X ⊆ M.E)
    (hY : Y ⊆ M.E) (hZ : Z ⊆ M.E) (hWX : Disjoint W X) (hWY : Disjoint W Y)
    (hWZ : Disjoint W Z) (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    W.ncard + X.ncard + Y.ncard + Z.ncard ≤ 4 * k + 2 := by
  have hf := h.finite
  have hWXf : (W ∪ X).Finite := (hf.subset hW).union (hf.subset hX)
  rw [← Set.ncard_union_eq hWX (hf.subset hW) (hf.subset hX),
    ← Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hWY, hXY⟩) hWXf (hf.subset hY),
    ← Set.ncard_union_eq
      (Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hWZ, hXZ⟩, hYZ⟩)
      (hWXf.union (hf.subset hY)) (hf.subset hZ), ← h.ncard_ground]
  exact Set.ncard_le_ncard (union_subset (union_subset (union_subset hW hX) hY) hZ) hf

/-- Pairwise disjoint subsets of the ground set have total size at most `4k+2`. -/
theorem sum_ncard_le (h : StrictT0 M k) {ι : Type*} (s : Finset ι) (G : ι → Set α)
    (hG : ∀ i, G i ⊆ M.E) (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (G i) (G j)) :
    ∑ i ∈ s, (G i).ncard ≤ 4 * k + 2 := by
  classical
  have key : ∀ t : Finset ι, t ⊆ s → ∑ i ∈ t, (G i).ncard = (⋃ i ∈ t, G i).ncard := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert a t ha ih =>
      intro hts
      have hat : a ∈ s := hts (Finset.mem_insert_self a t)
      have hts2 : t ⊆ s := (Finset.subset_insert a t).trans hts
      have hdisj : Disjoint (G a) (⋃ i ∈ t, G i) := by
        rw [Set.disjoint_iUnion₂_right]
        intro i hi
        exact hd a hat i (hts2 hi) fun hai => ha (by rw [hai]; exact hi)
      rw [Finset.sum_insert ha, Finset.set_biUnion_insert, ih hts2,
        Set.ncard_union_eq hdisj (h.finite.subset (hG a))
          (h.finite.subset (Set.iUnion₂_subset fun i _ => hG i))]
  rw [key s (Finset.Subset.refl s), ← h.ncard_ground]
  exact Set.ncard_le_ncard (Set.iUnion₂_subset fun i _ => hG i) h.finite

end StrictT0

/-- **A violated demand.** A basis `S` that does not meet the demands misses a demand flat `F`
of rank `r`: a `k`-point, a `2k`-line or a `(3k-1)`-plane disjoint from `S`, or a `3k`-plane
meeting `S` at most once. -/
theorem exists_viol (h : StrictT0 M k) {S : Set α} (hS : M.IsBase S)
    (hD : ¬ MeetsDemands M k S) :
    ∃ F : Set α, ∃ r : ℕ, M.IsFlat F ∧ M.eRk F = r ∧
      ((r = 1 ∧ F.ncard = k ∧ (S ∩ F).ncard = 0) ∨
        (r = 2 ∧ F.ncard = 2 * k ∧ (S ∩ F).ncard = 0) ∨
        (r = 3 ∧ F.ncard = 3 * k ∧ (S ∩ F).ncard ≤ 1) ∨
        (r = 3 ∧ F.ncard = 3 * k - 1 ∧ (S ∩ F).ncard = 0)) := by
  by_contra hno
  apply hD
  have hSfin : S.Finite := h.finite.subset hS.subset_ground
  have hcard : ∀ {F : Set α} {n : ℕ}, M.IsFlat F → F.encard = (n : ℕ∞) → F.ncard = n := by
    intro F n hF hc
    have h1 := (h.finite.subset hF.subset_ground).cast_ncard_eq
    rw [hc] at h1
    exact_mod_cast h1
  have hzero : ∀ {F : Set α}, ¬ (F ∩ S).Nonempty → (S ∩ F).ncard = 0 := by
    intro F hne
    rw [Set.inter_comm, Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty]
  refine ⟨fun F hF h1 hc => ?_, fun F hF h2 hc => ?_, fun F hF h3 hc => ?_,
    fun F hF h3 hc => ?_⟩
  · by_contra hne
    exact hno ⟨F, 1, hF, by exact_mod_cast h1, Or.inl ⟨rfl, hcard hF hc, hzero hne⟩⟩
  · by_contra hne
    exact hno ⟨F, 2, hF, by exact_mod_cast h2, Or.inr (Or.inl ⟨rfl, hcard hF hc, hzero hne⟩)⟩
  · by_contra hlt
    have hfin : (F ∩ S).Finite := hSfin.subset inter_subset_right
    have hle1 : (F ∩ S).ncard ≤ 1 := by
      by_contra hge
      apply hlt
      rw [← hfin.cast_ncard_eq]
      exact_mod_cast (by omega : 2 ≤ (F ∩ S).ncard)
    have heq : (S ∩ F).ncard = (F ∩ S).ncard := by rw [Set.inter_comm]
    exact hno ⟨F, 3, hF, by exact_mod_cast h3,
      Or.inr (Or.inr (Or.inl ⟨rfl, hcard hF hc, by omega⟩))⟩
  · by_contra hne
    exact hno ⟨F, 3, hF, by exact_mod_cast h3,
      Or.inr (Or.inr (Or.inr ⟨rfl, hcard hF hc, hzero hne⟩))⟩

end Hitting
end HigherRankKUM
