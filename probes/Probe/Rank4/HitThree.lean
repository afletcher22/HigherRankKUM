import Probe.Rank4.LemmaH
import HigherRankKUM.VHT.Covers
import HigherRankKUM.VHT.Theorem21

/-!
# The hitting lemma at `k = 3` with a heavy flat

Let `M` be strict with t=0 on `14` elements (`StrictT0 M 3`): no loops, points have at most `3`
elements, lines `6`, planes `9`. A basis `S` is deletable when `M \ S` has at most `2`, `5`, `7`
elements on every point, line, plane. Lemma H covers the case with no `9`-plane and no `6`-line.
This file proves the two other cases by hand. They were the certificates `hit14g` and
`hit14line`.

## A `9`-plane `K` (`hitG`)

This is the choice lemma of Theorem G at `k = 3` (`RANK4_HEAVY_FLAT_SPLICE.md` §7). Split `K`
into three bases `D₀, D₁, D₂` of `M ↾ K` (Edmonds), and let `C = E - K`, which has `5` elements.

* Choose `c ∈ C` so that `C₀ = C - c` has at most `2` elements on every point and `C ⊆ cl(C₀)`:
  `c` in the `3`-point inside `C` if there is one, else outside a basis of `C` (`exists_c`).
* A plane `F ≠ K` through `C` meets `K` in at most `4` elements. Two of the triples, `Da` and
  `Db`, meet every such plane in at most `3` elements together (`light_pair`). Otherwise some
  triple meets two such planes twice each, so it meets their intersection, which lies in
  `cl(C)`. Two triples would then meet `cl(C) ∩ K`, which has at most one element.
* Then `De + c` is deletable (`deletable_of_choice`). Let `X ⊆ E - (De + c)` have rank `j`. The
  part of `X` in `K` lies in `Da ∪ Db`, and the rest lies in `C₀`. If `X ⊆ K` then `|X| ≤ 2j`.
  Otherwise `X ∩ K` has rank less than `j`, and the bound can fail only if `X ⊇ C₀`. Then
  `cl(X) ⊇ C`. At rank `2`, `cl(X)` has at most one element in `K`. At rank `3`, `cl(X)` is a
  plane through `C`, and the choice of `Da`, `Db` applies.

## A `6`-line `L` and no `9`-plane (`hitLine`)

Here every plane has at most `8` elements. Every `3`-point lies in `L`. A second `6`-line `L'`
is disjoint from `L`, and there is at most one.

* Take `x ∉ L` on `L'` (if there is one), `y ∉ cl(L + x)`, and non-parallel `a, b ∈ L`. Then
  `S = {a, b, x, y}` is a basis and meets every `6`-line.
* An `8`-plane `F` that misses `x` and `y` and does not contain `L` meets `L` in a point with at
  least `2` elements. If the point has `3` elements, it is a `3`-point. If it has `2`, then
  `F - L` is all of `E - L - {x, y}`, so `F` is the closure of that set (`plane_eq`).
* So `a` and `b` only need to meet the `3`-points of `L` and one more point. Three such points
  would need `3 + 3 + 1 > 6` elements of `L` (`exists_pair_meeting`).
-/

namespace HigherRankKUM
namespace Hitting
namespace HitThree

open Set LemmaH
open scoped Matroid

variable {α : Type*} {M : Matroid α}

/-! ### Generic facts at `k = 3` -/

theorem ncard_le_three_mul (h : StrictT0 M 3) {X : Set α} (hX : X ⊆ M.E) {j : ℕ}
    (hr : M.eRk X ≤ j) (hj : j ≤ 3) : X.ncard ≤ 3 * j := by
  obtain ⟨i, hi, -⟩ := h.exists_eRk_eq X
  have hij : i ≤ j := by
    rw [hi] at hr
    exact_mod_cast hr
  have := h.ncard_le hX hi (by omega)
  omega

theorem ncard_of_encard (h : StrictT0 M 3) {X : Set α} (hX : X ⊆ M.E) {n : ℕ}
    (hc : X.encard = (n : ℕ∞)) : X.ncard = n := by
  rw [← (h.finite.subset hX).cast_ncard_eq] at hc
  exact_mod_cast hc

/-- An independent set meets a set of rank at most `j` in at most `j` elements. -/
theorem indep_inter_ncard_le (h : StrictT0 M 3) {D Y : Set α} (hD : M.Indep D) {j : ℕ}
    (hY : M.eRk Y ≤ j) : (D ∩ Y).ncard ≤ j := by
  have hfin : (D ∩ Y).Finite := h.finite.subset (inter_subset_left.trans hD.subset_ground)
  have h1 : M.eRk (D ∩ Y) = (D ∩ Y).encard := (hD.subset inter_subset_left).eRk_eq_encard
  have h2 : M.eRk (D ∩ Y) ≤ M.eRk Y := M.eRk_mono inter_subset_right
  rw [h1, ← hfin.cast_ncard_eq] at h2
  exact_mod_cast h2.trans hY

/-- A set of rank at most `1` lies in the closure of each of its elements. -/
theorem subset_closure_singleton_of_le_one (h : StrictT0 M 3) {Y : Set α} (hY : Y ⊆ M.E)
    (hYr : M.eRk Y ≤ 1) {e : α} (he : e ∈ Y) : Y ⊆ M.closure {e} :=
  subset_closure_of_eRk_le h.finite (singleton_subset_iff.2 he) hY
    (hYr.trans (one_le_eRk h (singleton_subset_iff.2 (hY he)) (singleton_nonempty e)))

/-- A set of rank at most `1` that meets a flat lies in it. -/
theorem subset_flat_of_le_one (h : StrictT0 M 3) {Y F : Set α} (hY : Y ⊆ M.E)
    (hYr : M.eRk Y ≤ 1) (hF : M.IsFlat F) {e : α} (heY : e ∈ Y) (heF : e ∈ F) : Y ⊆ F :=
  (subset_closure_singleton_of_le_one h hY hYr heY).trans
    ((M.closure_subset_closure (singleton_subset_iff.2 heF)).trans_eq hF.closure)

/-- Two flats of rank at most `1` that meet are equal. -/
theorem point_eq_of_meet (h : StrictT0 M 3) {P Q : Set α} (hP : M.IsFlat P) (hQ : M.IsFlat Q)
    (hPr : M.eRk P ≤ 1) (hQr : M.eRk Q ≤ 1) {e : α} (heP : e ∈ P) (heQ : e ∈ Q) : P = Q :=
  Subset.antisymm (subset_flat_of_le_one h hP.subset_ground hPr hQ heP heQ)
    (subset_flat_of_le_one h hQ.subset_ground hQr hP heQ heP)

/-- Two distinct flats of rank at most `1` are disjoint. -/
theorem point_disjoint_of_ne (h : StrictT0 M 3) {P Q : Set α} (hP : M.IsFlat P)
    (hQ : M.IsFlat Q) (hPr : M.eRk P ≤ 1) (hQr : M.eRk Q ≤ 1) (hne : P ≠ Q) : Disjoint P Q :=
  Set.disjoint_left.2 fun _ heP heQ => hne (point_eq_of_meet h hP hQ hPr hQr heP heQ)

/-- A set not inside the flat `F` meets it in a set of smaller rank. -/
theorem eRk_inter_flat_lt (h : StrictT0 M 3) {X F : Set α} (hX : X ⊆ M.E) (hF : M.IsFlat F)
    (hXF : ¬ X ⊆ F) : M.eRk (X ∩ F) < M.eRk X := by
  by_contra hle
  push_neg at hle
  exact hXF ((subset_closure_of_eRk_le h.finite inter_subset_left hX hle).trans
    ((M.closure_subset_closure inter_subset_right).trans_eq hF.closure))

theorem exists_eRk_inter_flat_lt (h : StrictT0 M 3) {X F : Set α} (hX : X ⊆ M.E)
    (hF : M.IsFlat F) (hXF : ¬ X ⊆ F) {j : ℕ} (hj : M.eRk X = j) :
    ∃ i : ℕ, M.eRk (X ∩ F) = i ∧ i < j := by
  obtain ⟨i, hi, -⟩ := h.exists_eRk_eq (X ∩ F)
  have hlt := eRk_inter_flat_lt h hX hF hXF
  rw [hi, hj] at hlt
  exact ⟨i, hi, by exact_mod_cast hlt⟩

/-- Two distinct flats of the same rank meet in a set of smaller rank. -/
theorem exists_eRk_inter_lt_of_ne (h : StrictT0 M 3) {F G : Set α} (hF : M.IsFlat F)
    (hG : M.IsFlat G) {j : ℕ} (hFr : M.eRk F = j) (hGr : M.eRk G = j) (hne : F ≠ G) :
    ∃ i : ℕ, M.eRk (F ∩ G) = i ∧ i < j := by
  have hFG : ¬ F ⊆ G := fun hsub => hne (Subset.antisymm hsub
    ((subset_closure_of_eRk_le h.finite hsub hG.subset_ground
      (le_of_eq (by rw [hFr, hGr]))).trans_eq hF.closure))
  exact exists_eRk_inter_flat_lt h hF.subset_ground hG hFG hFr

/-- `r(X ∪ Y) ≤ 3` from `r(X) ≤ a`, `r(Y) ≤ b` and `a + b ≤ 3`. -/
theorem eRk_union_le_three (h : StrictT0 M 3) {X Y : Set α} {a b : ℕ} (hX : M.eRk X ≤ a)
    (hY : M.eRk Y ≤ b) (hab : a + b ≤ 3) : M.eRk (X ∪ Y) ≤ 3 := by
  obtain ⟨u, hu, -⟩ := h.exists_eRk_eq (X ∪ Y)
  obtain ⟨s, hs, -⟩ := h.exists_eRk_eq X
  obtain ⟨t, ht, -⟩ := h.exists_eRk_eq Y
  have h1 := M.eRk_union_le_eRk_add_eRk X Y
  rw [hu, hs, ht] at h1
  rw [hs] at hX
  rw [ht] at hY
  have h1' : u ≤ s + t := by exact_mod_cast h1
  have hX' : s ≤ a := by exact_mod_cast hX
  have hY' : t ≤ b := by exact_mod_cast hY
  rw [hu]
  exact_mod_cast (show u ≤ 3 by omega)

/-- Inserting an element outside the closure keeps independence and adds one element. -/
theorem indep_insert_ncard (h : StrictT0 M 3) {I : Set α} (hI : M.Indep I) {e : α}
    (heE : e ∈ M.E) (he : e ∉ M.closure I) :
    M.Indep (insert e I) ∧ (insert e I).ncard = I.ncard + 1 := by
  have heI : e ∉ I := fun heI => he (M.subset_closure I hI.subset_ground heI)
  exact ⟨(hI.insert_indep_iff_of_notMem heI).2 ⟨heE, he⟩,
    Set.ncard_insert_of_notMem heI (h.finite.subset hI.subset_ground)⟩

/-- An independent set with `4` elements is a basis. -/
theorem isBase_of_indep_ncard (h : StrictT0 M 3) {S : Set α} (hS : M.Indep S)
    (hn : S.ncard = 4) : M.IsBase S := by
  have hfin : S.Finite := h.finite.subset hS.subset_ground
  have h4 : S.encard = (4 : ℕ∞) := by
    have := hfin.cast_ncard_eq
    rw [hn] at this
    exact_mod_cast this.symm
  exact hS.isBase_of_eRk_ge hfin (le_of_eq (by rw [h.rank, hS.eRk_eq_encard, h4]))

/-! ### A `6`-line and no `9`-plane -/

/-- No flat of rank `3` has `9` elements. -/
def NoNinePlane (M : Matroid α) : Prop :=
  ∀ F, M.IsFlat F → M.eRk F = 3 → F.encard ≠ ((3 * 3 : ℕ) : ℕ∞)

/-- A `6`-line: a flat of rank `2` with `6` elements. -/
def SixLine (M : Matroid α) (L : Set α) : Prop :=
  M.IsFlat L ∧ M.eRk L = 2 ∧ L.encard = ((2 * 3 : ℕ) : ℕ∞)

theorem SixLine.ncard (h : StrictT0 M 3) {L : Set α} (hL : SixLine M L) : L.ncard = 6 := by
  have := ncard_of_encard h hL.1.subset_ground hL.2.2
  omega

/-- With no `9`-plane, a set of rank at most `3` has at most `8` elements. -/
theorem ncard_le_eight (h : StrictT0 M 3) (h9 : NoNinePlane M) {X : Set α} (hX : X ⊆ M.E)
    (hr : M.eRk X ≤ 3) : X.ncard ≤ 8 := by
  obtain ⟨j, hj, -⟩ := h.exists_eRk_eq X
  have hj3 : j ≤ 3 := by
    rw [hj] at hr
    exact_mod_cast hr
  have hle := h.ncard_le hX hj hj3
  by_contra hbig
  have hj' : j = 3 := by omega
  subst hj'
  have hclE := M.closure_subset_ground X
  have hclfin : (M.closure X).Finite := h.finite.subset hclE
  have hcl1 := h.ncard_le hclE (j := 3) (by rw [M.eRk_closure_eq]; exact hj) le_rfl
  have hcl2 := Set.ncard_le_ncard (M.subset_closure X hX) hclfin
  apply h9 (M.closure X) (M.isFlat_closure X) (by rw [M.eRk_closure_eq]; exact_mod_cast hj)
  rw [← hclfin.cast_ncard_eq]
  exact_mod_cast (show (M.closure X).ncard = 3 * 3 by omega)

/-- With no `9`-plane, two distinct `6`-lines are disjoint: if they met, they would span a plane
with at least `9` elements. -/
theorem SixLine.disjoint (h : StrictT0 M 3) (h9 : NoNinePlane M) {L L' : Set α}
    (hL : SixLine M L) (hL' : SixLine M L') (hne : L ≠ L') : Disjoint L L' := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne'
  have hnon : (L ∩ L').Nonempty := Set.nonempty_iff_ne_empty.2 hne'
  have hLE := hL.1.subset_ground
  have hL'E := hL'.1.subset_ground
  have hLfin : L.Finite := h.finite.subset hLE
  have hL'fin : L'.Finite := h.finite.subset hL'E
  obtain ⟨v, hv, hv2⟩ := exists_eRk_inter_lt_of_ne h hL.1 hL'.1 (j := 2)
    (by exact_mod_cast hL.2.1) (by exact_mod_cast hL'.2.1) hne
  have hv1 : 1 ≤ v := by
    have := one_le_eRk h (inter_subset_left.trans hLE) hnon
    rw [hv] at this
    exact_mod_cast this
  obtain ⟨u, hu, -⟩ := h.exists_eRk_eq (L ∪ L')
  have hsubm := M.eRk_inter_add_eRk_union_le L L'
  rw [hv, hu, hL.2.1, hL'.2.1] at hsubm
  have hsubm' : v + u ≤ 2 + 2 := by exact_mod_cast hsubm
  have hU := ncard_le_eight h h9 (union_subset hLE hL'E)
    (by rw [hu]; exact_mod_cast (show u ≤ 3 by omega))
  have hI := ncard_le_three_mul h (inter_subset_left.trans hLE) (j := 1)
    (by rw [hv]; exact_mod_cast (show v ≤ 1 by omega)) (by norm_num)
  have hUI := Set.ncard_union_add_ncard_inter L L' hLfin hL'fin
  have := hL.ncard h
  have := hL'.ncard h
  omega

/-- With a `6`-line `L` and no `9`-plane, every `3`-point lies in `L`. -/
theorem point_subset_line (h : StrictT0 M 3) (h9 : NoNinePlane M) {L Q : Set α}
    (hL : SixLine M L) (hQ : M.IsFlat Q) (hQr : M.eRk Q = 1) (hQn : Q.ncard = 3) : Q ⊆ L := by
  by_cases hmeet : (Q ∩ L).Nonempty
  · obtain ⟨e, heQ, heL⟩ := hmeet
    exact subset_flat_of_le_one h hQ.subset_ground hQr.le hL.1 heQ heL
  · exfalso
    have hdisj : Disjoint Q L :=
      Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hmeet)
    have hQE := hQ.subset_ground
    have hLE := hL.1.subset_ground
    have hr : M.eRk (Q ∪ L) ≤ 3 :=
      eRk_union_le_three h (a := 1) (b := 2) (by exact_mod_cast hQr.le)
        (by exact_mod_cast hL.2.1.le) (by norm_num)
    have hU := ncard_le_eight h h9 (union_subset hQE hLE) hr
    have hUc := Set.ncard_union_eq hdisj (h.finite.subset hQE) (h.finite.subset hLE)
    have := hL.ncard h
    omega

/-- Some `x ∉ L` lies on every `6`-line other than `L`. -/
theorem exists_mem_lines (h : StrictT0 M 3) (h9 : NoNinePlane M) {L : Set α}
    (hL : SixLine M L) : ∃ x ∈ M.E, x ∉ L ∧ ∀ L', SixLine M L' → L' ≠ L → x ∈ L' := by
  have hLE := hL.1.subset_ground
  have hLfin : L.Finite := h.finite.subset hLE
  by_cases hex : ∃ L', SixLine M L' ∧ L' ≠ L
  · obtain ⟨L', hL', hne⟩ := hex
    have hL'E := hL'.1.subset_ground
    have hL'fin : L'.Finite := h.finite.subset hL'E
    obtain ⟨x, hx⟩ : L'.Nonempty :=
      (Set.ncard_pos hL'fin).1 (by have := hL'.ncard h; omega)
    refine ⟨x, hL'E hx, Set.disjoint_left.1 (hL'.disjoint h h9 hL hne) hx, ?_⟩
    intro L'' hL'' hne''
    by_contra hx''
    have hne2 : L' ≠ L'' := by
      intro hEq
      apply hx''
      rw [← hEq]
      exact hx
    -- three disjoint `6`-lines would need `18` elements
    have d1 := hL.disjoint h h9 hL' (Ne.symm hne)
    have d2 := hL.disjoint h h9 hL'' (Ne.symm hne'')
    have d3 := hL'.disjoint h h9 hL'' hne2
    have hL''E := hL''.1.subset_ground
    have hL''fin : L''.Finite := h.finite.subset hL''E
    have h12 := Set.ncard_union_eq d1 hLfin hL'fin
    have h123 := Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d2, d3⟩) (hLfin.union hL'fin)
      hL''fin
    have hsub := Set.ncard_le_ncard (union_subset (union_subset hLE hL'E) hL''E) h.finite
    have := h.ncard_ground
    have := hL.ncard h
    have := hL'.ncard h
    have := hL''.ncard h
    omega
  · have hnot : ¬ M.E ⊆ L := fun hsub => by
      have := Set.ncard_le_ncard hsub hLfin
      have := h.ncard_ground
      have := hL.ncard h
      omega
    obtain ⟨x, hxE, hxL⟩ := Set.not_subset.1 hnot
    exact ⟨x, hxE, hxL, fun L' hL' hne => (hex ⟨L', hL', hne⟩).elim⟩

/-- Some element lies outside `cl(L + x)`, a set of rank at most `3`. -/
theorem exists_not_mem_closure (h : StrictT0 M 3) (h9 : NoNinePlane M) {L : Set α}
    (hL : SixLine M L) (x : α) : ∃ y ∈ M.E, y ∉ M.closure (insert x L) := by
  by_contra hc
  push_neg at hc
  have hclE := M.closure_subset_ground (insert x L)
  have hr : M.eRk (M.closure (insert x L)) ≤ 3 := by
    rw [M.eRk_closure_eq, Set.insert_eq]
    exact eRk_union_le_three h (a := 1) (b := 2) (by exact_mod_cast M.eRk_singleton_le x)
      (by exact_mod_cast hL.2.1.le) (by norm_num)
  have h1 := ncard_le_eight h h9 hclE hr
  have h2 := Set.ncard_le_ncard (fun y hy => hc y hy) (h.finite.subset hclE)
  have h3 := h.ncard_ground
  omega

/-- A subset of `E` avoiding the `6`-line `L` and two further elements has at most `6`
elements. -/
theorem ncard_le_six_avoid (h : StrictT0 M 3) {L A : Set α} (hL : SixLine M L) {x y : α}
    (hxE : x ∈ M.E) (hyE : y ∈ M.E) (hxL : x ∉ L) (hyL : y ∉ L) (hxy : x ≠ y)
    (hA : A ⊆ M.E) (hAL : Disjoint A L) (hxA : x ∉ A) (hyA : y ∉ A) : A.ncard ≤ 6 := by
  have hLE := hL.1.subset_ground
  have hLfin : L.Finite := h.finite.subset hLE
  have hAfin : A.Finite := h.finite.subset hA
  have hd1 : Disjoint A {x, y} := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases hz' with hzx | hzy
    · exact hxA (by rw [← hzx]; exact hz)
    · exact hyA (by rw [← Set.mem_singleton_iff.1 hzy]; exact hz)
  have hd2 : Disjoint (A ∪ {x, y}) L := by
    rw [Set.disjoint_union_left]
    refine ⟨hAL, ?_⟩
    rw [Set.disjoint_left]
    intro z hz hzL
    rcases hz with hzx | hzy
    · exact hxL (by rw [← hzx]; exact hzL)
    · exact hyL (by rw [← Set.mem_singleton_iff.1 hzy]; exact hzL)
  have hU1 := Set.ncard_union_eq hd1 hAfin (Set.toFinite {x, y})
  have hU2 := Set.ncard_union_eq hd2 (hAfin.union (Set.toFinite {x, y})) hLfin
  have hsub : A ∪ {x, y} ∪ L ⊆ M.E :=
    union_subset (union_subset hA (insert_subset hxE (singleton_subset_iff.2 hyE))) hLE
  have hle := Set.ncard_le_ncard hsub h.finite
  have hxy2 : ({x, y} : Set α).ncard = 2 := Set.ncard_pair hxy
  have := h.ncard_ground
  have := hL.ncard h
  omega

/-- If the plane `F` misses `x` and `y`, and `F - L` has `6` elements, then `F` is the closure of
`E - L - {x, y}`. -/
theorem plane_eq (h : StrictT0 M 3) {L F : Set α} (hL : SixLine M L) {x y : α}
    (hxE : x ∈ M.E) (hyE : y ∈ M.E) (hxL : x ∉ L) (hyL : y ∉ L) (hxy : x ≠ y)
    (hxlines : ∀ L', SixLine M L' → L' ≠ L → x ∈ L')
    (hFf : M.IsFlat F) (hFr : M.eRk F = 3) (hxF : x ∉ F) (hyF : y ∉ F)
    (hF6 : (F \ L).ncard = 6) : F = M.closure ((M.E \ L) \ {x, y}) := by
  have hFE := hFf.subset_ground
  have hWE : (M.E \ L) \ {x, y} ⊆ M.E := Set.sdiff_subset.trans Set.sdiff_subset
  have hWfin : ((M.E \ L) \ {x, y}).Finite := h.finite.subset hWE
  have hxW : x ∉ (M.E \ L) \ {x, y} := fun hx => hx.2 (mem_insert x _)
  have hyW : y ∉ (M.E \ L) \ {x, y} := fun hy => hy.2 (mem_insert_of_mem x (mem_singleton y))
  have hW6 := ncard_le_six_avoid h hL hxE hyE hxL hyL hxy hWE
    (Set.disjoint_left.2 fun _ hz hzL => hz.1.2 hzL) hxW hyW
  have hFW : F \ L ⊆ (M.E \ L) \ {x, y} := by
    intro z hz
    refine ⟨⟨hFE hz.1, hz.2⟩, ?_⟩
    rintro (hzx | hzy)
    · exact hxF (by rw [← hzx]; exact hz.1)
    · exact hyF (by rw [← Set.mem_singleton_iff.1 hzy]; exact hz.1)
  have hEq : F \ L = (M.E \ L) \ {x, y} := Set.eq_of_subset_of_ncard_le hFW (by omega) hWfin
  have hWF : (M.E \ L) \ {x, y} ⊆ F := by
    rw [← hEq]
    exact Set.sdiff_subset
  have hWn : ((M.E \ L) \ {x, y}).ncard = 6 := by
    rw [← hEq]
    exact hF6
  -- `E - L - {x, y}` has rank `3`: otherwise its closure is a second `6`-line, missing `x`
  have hWr : M.eRk F ≤ M.eRk ((M.E \ L) \ {x, y}) := by
    rw [hFr]
    obtain ⟨j, hj, -⟩ := h.exists_eRk_eq ((M.E \ L) \ {x, y})
    rw [hj]
    by_contra hj3
    have hj2 : j ≤ 2 := by
      by_contra hj2
      exact hj3 (by exact_mod_cast (show 3 ≤ j by omega))
    have hle := h.ncard_le hWE hj (by omega)
    have hj2' : j = 2 := by omega
    subst hj2'
    have hclE := M.closure_subset_ground ((M.E \ L) \ {x, y})
    have hclfin : (M.closure ((M.E \ L) \ {x, y})).Finite := h.finite.subset hclE
    have hcl6 := h.ncard_le hclE (j := 2) (by rw [M.eRk_closure_eq]; exact hj) (by norm_num)
    have hsub := M.subset_closure _ hWE
    have hclW : M.closure ((M.E \ L) \ {x, y}) = (M.E \ L) \ {x, y} :=
      (Set.eq_of_subset_of_ncard_le hsub (by omega) hclfin).symm
    have hcln : (M.closure ((M.E \ L) \ {x, y})).ncard = 2 * 3 := by
      rw [hclW]
      omega
    have hline : SixLine M (M.closure ((M.E \ L) \ {x, y})) := by
      refine ⟨M.isFlat_closure _, by rw [M.eRk_closure_eq]; exact_mod_cast hj, ?_⟩
      rw [← hclfin.cast_ncard_eq, hcln]
    have hne : M.closure ((M.E \ L) \ {x, y}) ≠ L := by
      intro hEqL
      obtain ⟨w, hw⟩ : ((M.E \ L) \ {x, y}).Nonempty := (Set.ncard_pos hWfin).1 (by omega)
      apply hw.1.2
      rw [← hEqL]
      exact hsub hw
    have hx := hxlines _ hline hne
    rw [hclW] at hx
    exact hxW hx
  exact Subset.antisymm (subset_closure_of_eRk_le h.finite hWF hFE hWr)
    ((M.closure_subset_closure hWF).trans_eq hFf.closure)

/-- Two non-parallel elements of the `6`-line `L` that meet every `3`-point inside `L`, and also
`Z` if `Z` is a point inside `L`. -/
theorem exists_pair_meeting (h : StrictT0 M 3) {L : Set α} (hL : SixLine M L) (Z : Set α) :
    ∃ a ∈ L, ∃ b ∈ L, b ∉ M.closure {a} ∧ ∀ Q, M.IsFlat Q → M.eRk Q = 1 → Q ⊆ L →
      (Q.ncard = 3 ∨ Q = Z) → a ∈ Q ∨ b ∈ Q := by
  have hLE := hL.1.subset_ground
  have hLfin : L.Finite := h.finite.subset hLE
  have hLn := hL.ncard h
  have hne : ∀ Q : Set α, M.eRk Q = 1 → Q.Nonempty := by
    intro Q hQ
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    rw [M.eRk_empty] at hQ
    exact zero_ne_one hQ
  have hother : ∀ a ∈ L, ∃ b ∈ L, b ∉ M.closure {a} := by
    intro a ha
    by_contra hc
    push_neg at hc
    have hr := M.eRk_mono (show L ⊆ M.closure {a} from fun b hb => hc b hb)
    rw [M.eRk_closure_eq, hL.2.1] at hr
    have h21 : (2 : ℕ) ≤ 1 := by exact_mod_cast hr.trans (M.eRk_singleton_le a)
    omega
  by_cases h1 : ∃ Q, M.IsFlat Q ∧ M.eRk Q = 1 ∧ Q ⊆ L ∧ (Q.ncard = 3 ∨ Q = Z)
  · obtain ⟨Q1, hQ1f, hQ1r, hQ1L, hQ1c⟩ := h1
    obtain ⟨a, ha⟩ := hne Q1 hQ1r
    by_cases h2 : ∃ Q, M.IsFlat Q ∧ M.eRk Q = 1 ∧ Q ⊆ L ∧ (Q.ncard = 3 ∨ Q = Z) ∧ Q ≠ Q1
    · obtain ⟨Q2, hQ2f, hQ2r, hQ2L, hQ2c, hne21⟩ := h2
      obtain ⟨b, hb⟩ := hne Q2 hQ2r
      have d12 := point_disjoint_of_ne h hQ1f hQ2f hQ1r.le hQ2r.le (Ne.symm hne21)
      refine ⟨a, hQ1L ha, b, hQ2L hb, ?_, ?_⟩
      · intro hb1
        have hbQ1 : b ∈ Q1 :=
          ((M.closure_subset_closure (singleton_subset_iff.2 ha)).trans_eq hQ1f.closure) hb1
        exact Set.disjoint_left.1 d12 hbQ1 hb
      · -- a third point would need `3 + 3 + 1 > 6` elements of `L`
        intro Q hQf hQr hQL hQc
        by_contra hab
        push_neg at hab
        have hQ1' : Q ≠ Q1 := fun hEq => hab.1 (by rw [hEq]; exact ha)
        have hQ2' : Q ≠ Q2 := fun hEq => hab.2 (by rw [hEq]; exact hb)
        have d13 := point_disjoint_of_ne h hQ1f hQf hQ1r.le hQr.le (Ne.symm hQ1')
        have d23 := point_disjoint_of_ne h hQ2f hQf hQ2r.le hQr.le (Ne.symm hQ2')
        have n1 := (Set.ncard_pos (hLfin.subset hQ1L)).2 ⟨a, ha⟩
        have n2 := (Set.ncard_pos (hLfin.subset hQ2L)).2 ⟨b, hb⟩
        have n3 := (Set.ncard_pos (hLfin.subset hQL)).2 (hne Q hQr)
        have hU1 := Set.ncard_union_eq d12 (hLfin.subset hQ1L) (hLfin.subset hQ2L)
        have hU2 := Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d13, d23⟩)
          ((hLfin.subset hQ1L).union (hLfin.subset hQ2L)) (hLfin.subset hQL)
        have hsub := Set.ncard_le_ncard (union_subset (union_subset hQ1L hQ2L) hQL) hLfin
        rcases hQ1c with c1 | e1 <;> rcases hQ2c with c2 | e2 <;> rcases hQc with c3 | e3 <;>
          first
          | omega
          | exact hQ1' (e3.trans e1.symm)
          | exact hQ2' (e3.trans e2.symm)
          | exact hne21 (e2.trans e1.symm)
    · obtain ⟨b, hbL, hb⟩ := hother a (hQ1L ha)
      refine ⟨a, hQ1L ha, b, hbL, hb, fun Q hQf hQr hQL hQc => Or.inl ?_⟩
      have hQQ1 : Q = Q1 := by
        by_contra hQ1'
        exact h2 ⟨Q, hQf, hQr, hQL, hQc, hQ1'⟩
      rw [hQQ1]
      exact ha
  · obtain ⟨a, ha⟩ : L.Nonempty := (Set.ncard_pos hLfin).1 (by omega)
    obtain ⟨b, hbL, hb⟩ := hother a ha
    exact ⟨a, ha, b, hbL, hb, fun Q hQf hQr hQL hQc => (h1 ⟨Q, hQf, hQr, hQL, hQc⟩).elim⟩

/-- **The `6`-line case** (formerly the certificate `hit14line`): with a `6`-line and no
`9`-plane, some basis meets the demands. -/
theorem hitLine (h : StrictT0 M 3) {L : Set α} (hLf : M.IsFlat L) (hLr : M.eRk L = 2)
    (hLc : L.encard = ((2 * 3 : ℕ) : ℕ∞)) (h9 : NoNinePlane M) :
    ∃ S, M.IsBase S ∧ MeetsDemands M 3 S := by
  have hL : SixLine M L := ⟨hLf, hLr, hLc⟩
  have hLE := hLf.subset_ground
  have hLfin : L.Finite := h.finite.subset hLE
  have hLn := hL.ncard h
  obtain ⟨x, hxE, hxL, hxlines⟩ := exists_mem_lines h h9 hL
  obtain ⟨y, hyE, hycl⟩ := exists_not_mem_closure h h9 hL x
  have hxLE : insert x L ⊆ M.E := insert_subset hxE hLE
  have hyL : y ∉ L := fun hy => hycl (M.subset_closure _ hxLE (mem_insert_of_mem x hy))
  have hyx : y ≠ x := by
    intro hyx
    apply hycl
    rw [hyx]
    exact M.subset_closure _ hxLE (mem_insert x L)
  obtain ⟨a, haL, b, hbL, hab, hpts⟩ :=
    exists_pair_meeting h hL (L ∩ M.closure ((M.E \ L) \ {x, y}))
  have haE := hLE haL
  have hbE := hLE hbL
  -- `S = {a, b, x, y}` is a basis
  have hIa : M.Indep {a} := by
    refine (Matroid.indep_iff_eRk_eq_encard_of_finite (M := M) (Set.finite_singleton a)).2 ?_
    rw [Set.encard_singleton]
    exact le_antisymm (M.eRk_singleton_le a)
      (one_le_eRk h (singleton_subset_iff.2 haE) (singleton_nonempty a))
  have hab2 : insert b {a} ⊆ L := insert_subset hbL (singleton_subset_iff.2 haL)
  have hclab : M.closure (insert b {a}) ⊆ L :=
    (M.closure_subset_closure hab2).trans_eq hLf.closure
  obtain ⟨hI2, hn2⟩ := indep_insert_ncard h hIa hbE hab
  obtain ⟨hI3, hn3⟩ := indep_insert_ncard h hI2 hxE (fun hx => hxL (hclab hx))
  obtain ⟨hI4, hn4⟩ := indep_insert_ncard h hI3 hyE
    (fun hy => hycl (M.closure_subset_closure (insert_subset_insert hab2) hy))
  have hS := isBase_of_indep_ncard h hI4 (by have := Set.ncard_singleton a; omega)
  have haS : a ∈ insert y (insert x (insert b {a})) :=
    mem_insert_of_mem _ (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton a)))
  have hbS : b ∈ insert y (insert x (insert b {a})) :=
    mem_insert_of_mem _ (mem_insert_of_mem _ (mem_insert b _))
  have hxS : x ∈ insert y (insert x (insert b {a})) := mem_insert_of_mem _ (mem_insert x _)
  have hyS : y ∈ insert y (insert x (insert b {a})) := mem_insert y _
  refine ⟨insert y (insert x (insert b {a})), hS, ?_, ?_, ?_, ?_⟩
  · -- `3`-points lie in `L`
    intro Q hQf hQr hQc
    have hQn := ncard_of_encard h hQf.subset_ground hQc
    rcases hpts Q hQf hQr (point_subset_line h h9 hL hQf hQr hQn) (Or.inl hQn) with ha | hb
    · exact ⟨a, ha, haS⟩
    · exact ⟨b, hb, hbS⟩
  · -- `6`-lines: `L` and at most one more, through `x`
    intro F hFf hFr hFc
    by_cases hFL : F = L
    · exact ⟨a, by rw [hFL]; exact haL, haS⟩
    · exact ⟨x, hxlines F ⟨hFf, hFr, hFc⟩ hFL, hxS⟩
  · -- no `9`-planes
    intro F hFf hFr hFc
    exact absurd hFc (h9 F hFf hFr)
  · -- `8`-planes
    intro F hFf hFr hFc
    have hFE := hFf.subset_ground
    have hFfin : F.Finite := h.finite.subset hFE
    have hFn := ncard_of_encard h hFE hFc
    by_cases hxF : x ∈ F
    · exact ⟨x, hxF, hxS⟩
    by_cases hyF : y ∈ F
    · exact ⟨y, hyF, hyS⟩
    by_cases hLF : L ⊆ F
    · exact ⟨a, hLF haL, haS⟩
    -- `L ∩ F` is a point with `2` or `3` elements
    have hQf : M.IsFlat (L ∩ F) := isFlat_inter hLf hFf
    obtain ⟨i, hi, hi2⟩ := exists_eRk_inter_flat_lt h hLE hFf hLF (j := 2)
      (by exact_mod_cast hLr)
    have hQ3 := ncard_le_three_mul h (inter_subset_left.trans hLE) (j := 1)
      (by rw [hi]; exact_mod_cast (show i ≤ 1 by omega)) (by norm_num)
    have hFL6 := ncard_le_six_avoid h hL hxE hyE hxL hyL (Ne.symm hyx)
      (Set.sdiff_subset.trans hFE) Set.disjoint_sdiff_left (fun hx => hxF hx.1) (fun hy => hyF hy.1)
    have hsplit : (L ∩ F).ncard + (F \ L).ncard = F.ncard := by
      rw [Set.inter_comm]
      exact Set.ncard_inter_add_ncard_sdiff_eq_ncard F L hFfin
    have hQne : (L ∩ F).Nonempty := (Set.ncard_pos (hLfin.subset inter_subset_left)).1 (by omega)
    have hQr : M.eRk (L ∩ F) = 1 := by
      have h1 := one_le_eRk h (inter_subset_left.trans hLE) hQne
      rw [hi] at h1 ⊢
      have : 1 ≤ i := by exact_mod_cast h1
      exact_mod_cast (show i = 1 by omega)
    have hcase : (L ∩ F).ncard = 3 ∨ L ∩ F = L ∩ M.closure ((M.E \ L) \ {x, y}) := by
      by_cases h3 : (L ∩ F).ncard = 3
      · exact Or.inl h3
      · right
        have hF6 : (F \ L).ncard = 6 := by omega
        rw [plane_eq h hL hxE hyE hxL hyL (Ne.symm hyx) hxlines hFf hFr hxF hyF hF6]
    rcases hpts (L ∩ F) hQf hQr inter_subset_left hcase with ha | hb
    · exact ⟨a, ha.2, haS⟩
    · exact ⟨b, hb.2, hbS⟩

/-! ### A `9`-plane -/

/-- `Da` and `Db` are *light*: every plane `F ≠ K` through `E - K` meets them in at most `3`
elements together. -/
def LightPair (M : Matroid α) (K Da Db : Set α) : Prop :=
  ∀ F, M.IsFlat F → M.eRk F = 3 → F ≠ K → M.E \ K ⊆ F → (F ∩ Da).ncard + (F ∩ Db).ncard ≤ 3

theorem ncard_diff_nine (h : StrictT0 M 3) {K : Set α} (hKE : K ⊆ M.E) (hKn : K.ncard = 9) :
    (M.E \ K).ncard = 5 := by
  have h1 := Set.ncard_sdiff_add_ncard_of_subset hKE h.finite
  have h2 := h.ncard_ground
  omega

/-- A plane through `E - K` meets `K` in at most `4` elements. -/
theorem ncard_inter_le_four (h : StrictT0 M 3) {K F : Set α} (hKE : K ⊆ M.E)
    (hKn : K.ncard = 9) (hF : M.IsFlat F) (hFr : M.eRk F = 3) (hCF : M.E \ K ⊆ F) :
    (F ∩ K).ncard ≤ 4 := by
  have hFE := hF.subset_ground
  have hFn := ncard_le_three_mul h hFE (j := 3) (by exact_mod_cast hFr.le) le_rfl
  have hdisj : Disjoint (F ∩ K) (M.E \ K) := Set.disjoint_left.2 fun _ hz hz' => hz'.2 hz.2
  have hU := Set.ncard_union_eq hdisj (h.finite.subset (inter_subset_left.trans hFE))
    (h.finite.subset Set.sdiff_subset)
  have hle := Set.ncard_le_ncard (union_subset (inter_subset_left : F ∩ K ⊆ F) hCF)
    (h.finite.subset hFE)
  have hCn := ncard_diff_nine h hKE hKn
  omega

/-- A plane `F ≠ K` meets an independent subset of the plane `K` in at most `2` elements. -/
theorem ncard_inter_le_two (h : StrictT0 M 3) {K F D : Set α} (hKf : M.IsFlat K)
    (hKr : M.eRk K = 3) (hF : M.IsFlat F) (hFr : M.eRk F = 3) (hFK : F ≠ K) (hD : M.Indep D)
    (hDK : D ⊆ K) : (F ∩ D).ncard ≤ 2 := by
  obtain ⟨i, hi, hi3⟩ := exists_eRk_inter_lt_of_ne h hF hKf (j := 3) (by exact_mod_cast hFr)
    (by exact_mod_cast hKr) hFK
  have h1 := indep_inter_ncard_le h hD (Y := F ∩ K) hi.le
  have h2 : (F ∩ D).ncard ≤ (D ∩ (F ∩ K)).ncard :=
    Set.ncard_le_ncard (fun z hz => ⟨hz.2, hz.1, hDK hz.2⟩)
      (h.finite.subset (inter_subset_left.trans hD.subset_ground))
  omega

theorem heavy_of_not_light (h : StrictT0 M 3) {K Da Db : Set α} (hKf : M.IsFlat K)
    (hKr : M.eRk K = 3) (hDa : M.Indep Da) (hDb : M.Indep Db) (hDaK : Da ⊆ K) (hDbK : Db ⊆ K)
    (hno : ¬ LightPair M K Da Db) :
    ∃ F, M.IsFlat F ∧ M.eRk F = 3 ∧ F ≠ K ∧ M.E \ K ⊆ F ∧
      2 ≤ (F ∩ Da).ncard ∧ 2 ≤ (F ∩ Db).ncard := by
  unfold LightPair at hno
  push_neg at hno
  obtain ⟨F, hF, hFr, hFK, hCF, hlt⟩ := hno
  have ha := ncard_inter_le_two h hKf hKr hF hFr hFK hDa hDaK
  have hb := ncard_inter_le_two h hKf hKr hF hFr hFK hDb hDbK
  exact ⟨F, hF, hFr, hFK, hCF, by omega, by omega⟩

/-- Two distinct planes through `E - K` meet inside `cl(E - K)`, and `cl(E - K)` meets `K` in at
most one element. -/
theorem inter_subset_closure_compl (h : StrictT0 M 3) {K F G : Set α} (hKE : K ⊆ M.E)
    (hKn : K.ncard = 9) (hF : M.IsFlat F) (hFr : M.eRk F = 3) (hG : M.IsFlat G)
    (hGr : M.eRk G = 3) (hFG : F ≠ G) (hCF : M.E \ K ⊆ F) (hCG : M.E \ K ⊆ G) :
    F ∩ G ⊆ M.closure (M.E \ K) ∧ (M.closure (M.E \ K) ∩ K).ncard ≤ 1 := by
  have hCE : M.E \ K ⊆ M.E := Set.sdiff_subset
  have hCn := ncard_diff_nine h hKE hKn
  obtain ⟨i, hi, hi3⟩ := exists_eRk_inter_lt_of_ne h hF hG (j := 3) (by exact_mod_cast hFr)
    (by exact_mod_cast hGr) hFG
  -- `E - K` has rank at least `2`, and at most `r(F ∩ G) ≤ 2`
  obtain ⟨s, hs, -⟩ := h.exists_eRk_eq (M.E \ K)
  have hs2 : 2 ≤ s := by
    by_contra hs2
    have := h.ncard_le hCE hs (by omega)
    omega
  have hsi : s ≤ i := by
    have := M.eRk_mono (subset_inter hCF hCG)
    rw [hs, hi] at this
    exact_mod_cast this
  have hsub : F ∩ G ⊆ M.closure (M.E \ K) :=
    subset_closure_of_eRk_le h.finite (subset_inter hCF hCG)
      (inter_subset_left.trans hF.subset_ground)
      (by rw [hi, hs]; exact_mod_cast (show i ≤ s by omega))
  refine ⟨hsub, ?_⟩
  have hclE := M.closure_subset_ground (M.E \ K)
  have hcl6 := ncard_le_three_mul h hclE (j := 2)
    (by rw [M.eRk_closure_eq, hs]; exact_mod_cast (show s ≤ 2 by omega)) (by norm_num)
  have hdisj : Disjoint (M.closure (M.E \ K) ∩ K) (M.E \ K) :=
    Set.disjoint_left.2 fun _ hz hz' => hz'.2 hz.2
  have hU := Set.ncard_union_eq hdisj (h.finite.subset (inter_subset_left.trans hclE))
    (h.finite.subset hCE)
  have hle := Set.ncard_le_ncard
    (union_subset (inter_subset_left : M.closure (M.E \ K) ∩ K ⊆ M.closure (M.E \ K))
      (M.subset_closure _ hCE)) (h.finite.subset hclE)
  omega

/-- Two subsets of a `3`-element set with at least `2` elements each meet. -/
theorem nonempty_inter_of_two_le {D A B : Set α} (hD : D.Finite) (hDn : D.ncard = 3)
    (hA : A ⊆ D) (hB : B ⊆ D) (hAn : 2 ≤ A.ncard) (hBn : 2 ≤ B.ncard) : (A ∩ B).Nonempty := by
  by_contra hne
  have hdisj : Disjoint A B :=
    Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne)
  have hU := Set.ncard_union_eq hdisj (hD.subset hA) (hD.subset hB)
  have hle := Set.ncard_le_ncard (union_subset hA hB) hD
  omega

/-- **The heavy-plane lemma.** Of three disjoint independent triples in the `9`-plane `K`, some
two are light. -/
theorem light_pair (h : StrictT0 M 3) {K D0 D1 D2 : Set α} (hKf : M.IsFlat K)
    (hKr : M.eRk K = 3) (hKn : K.ncard = 9) (hD0 : M.Indep D0) (hD1 : M.Indep D1)
    (hD2 : M.Indep D2) (hD0K : D0 ⊆ K) (hD1K : D1 ⊆ K) (hD2K : D2 ⊆ K) (hD0n : D0.ncard = 3)
    (hD1n : D1.ncard = 3) (h01 : Disjoint D0 D1) (h02 : Disjoint D0 D2)
    (h12 : Disjoint D1 D2) :
    LightPair M K D0 D1 ∨ LightPair M K D0 D2 ∨ LightPair M K D1 D2 := by
  have hKE := hKf.subset_ground
  by_contra hno
  simp only [not_or] at hno
  obtain ⟨n01, n02, n12⟩ := hno
  obtain ⟨F01, hF01, hF01r, -, hCF01, a0, a1⟩ :=
    heavy_of_not_light h hKf hKr hD0 hD1 hD0K hD1K n01
  obtain ⟨F02, hF02, hF02r, -, hCF02, b0, b2⟩ :=
    heavy_of_not_light h hKf hKr hD0 hD2 hD0K hD2K n02
  obtain ⟨F12, hF12, hF12r, -, hCF12, c1, c2⟩ :=
    heavy_of_not_light h hKf hKr hD1 hD2 hD1K hD2K n12
  -- a plane through `E - K` meets `K` in at most `4` elements, so not all triples twice
  have three : ∀ F, M.IsFlat F → M.eRk F = 3 → M.E \ K ⊆ F → 2 ≤ (F ∩ D0).ncard →
      2 ≤ (F ∩ D1).ncard → 2 ≤ (F ∩ D2).ncard → False := by
    intro F hF hFr hCF n0 n1 n2
    have h4 := ncard_inter_le_four h hKE hKn hF hFr hCF
    have hFE := hF.subset_ground
    have hfin : ∀ {Y : Set α}, Y ⊆ F → Y.Finite := fun hY => h.finite.subset (hY.trans hFE)
    have d01 : Disjoint (F ∩ D0) (F ∩ D1) :=
      Set.disjoint_of_subset inter_subset_right inter_subset_right h01
    have d02 : Disjoint (F ∩ D0) (F ∩ D2) :=
      Set.disjoint_of_subset inter_subset_right inter_subset_right h02
    have d12 : Disjoint (F ∩ D1) (F ∩ D2) :=
      Set.disjoint_of_subset inter_subset_right inter_subset_right h12
    have hU1 := Set.ncard_union_eq d01 (hfin inter_subset_left) (hfin inter_subset_left)
    have hU2 := Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d02, d12⟩)
      ((hfin inter_subset_left).union (hfin inter_subset_left)) (hfin inter_subset_left)
    have hsub : (F ∩ D0) ∪ (F ∩ D1) ∪ (F ∩ D2) ⊆ F ∩ K :=
      union_subset
        (union_subset (inter_subset_inter_right F hD0K) (inter_subset_inter_right F hD1K))
        (inter_subset_inter_right F hD2K)
    have hle := Set.ncard_le_ncard hsub (hfin inter_subset_left)
    omega
  have hne1 : F01 ≠ F02 := by
    intro hEq
    rw [← hEq] at b2
    exact three F01 hF01 hF01r hCF01 a0 a1 b2
  have hne2 : F01 ≠ F12 := by
    intro hEq
    rw [← hEq] at c2
    exact three F01 hF01 hF01r hCF01 a0 a1 c2
  -- `D0` meets `F01 ∩ F02` and `D1` meets `F01 ∩ F12`, both inside `cl(E - K) ∩ K`
  have hD0fin : D0.Finite := h.finite.subset (hD0K.trans hKE)
  have hD1fin : D1.Finite := h.finite.subset (hD1K.trans hKE)
  obtain ⟨p, hp1, hp2⟩ :=
    nonempty_inter_of_two_le hD0fin hD0n inter_subset_right inter_subset_right a0 b0
  obtain ⟨q, hq1, hq2⟩ :=
    nonempty_inter_of_two_le hD1fin hD1n inter_subset_right inter_subset_right a1 c1
  obtain ⟨hsub1, hcl1⟩ :=
    inter_subset_closure_compl h hKE hKn hF01 hF01r hF02 hF02r hne1 hCF01 hCF02
  obtain ⟨hsub2, -⟩ :=
    inter_subset_closure_compl h hKE hKn hF01 hF01r hF12 hF12r hne2 hCF01 hCF12
  have hpC : p ∈ M.closure (M.E \ K) ∩ K := ⟨hsub1 ⟨hp1.1, hp2.1⟩, hD0K hp1.2⟩
  have hqC : q ∈ M.closure (M.E \ K) ∩ K := ⟨hsub2 ⟨hq1.1, hq2.1⟩, hD1K hq1.2⟩
  have hpq : p ≠ q := by
    intro hEq
    rw [hEq] at hp1
    exact Set.disjoint_left.1 h01 hp1.2 hq1.2
  have h2 := Set.ncard_le_ncard (insert_subset hpC (singleton_subset_iff.2 hqC))
    (h.finite.subset (inter_subset_left.trans (M.closure_subset_ground _)))
  rw [Set.ncard_pair hpq] at h2
  omega

/-- Some `c ∉ K` leaves at most `2` elements of every point in `C₀ = E - K - c`, with
`E - K ⊆ cl(C₀)`. -/
theorem exists_c (h : StrictT0 M 3) {K : Set α} (hKf : M.IsFlat K) (hKn : K.ncard = 9) :
    ∃ c ∈ M.E, c ∉ K ∧ (∀ Y ⊆ (M.E \ K) \ {c}, M.eRk Y ≤ 1 → Y.ncard ≤ 2) ∧
      M.E \ K ⊆ M.closure ((M.E \ K) \ {c}) := by
  have hKE := hKf.subset_ground
  have hCE : M.E \ K ⊆ M.E := Set.sdiff_subset
  have hCfin : (M.E \ K).Finite := h.finite.subset hCE
  have hCn := ncard_diff_nine h hKE hKn
  by_cases hQ : ∃ Q ⊆ M.E \ K, M.eRk Q ≤ 1 ∧ 3 ≤ Q.ncard
  · -- `c` in the `3`-point `Q` inside `E - K`
    obtain ⟨Q, hQC, hQr, hQn⟩ := hQ
    have hQfin : Q.Finite := hCfin.subset hQC
    obtain ⟨c, hcQ⟩ : Q.Nonempty := (Set.ncard_pos hQfin).1 (by omega)
    obtain ⟨c', hc'Q, hc'c⟩ : ∃ c' ∈ Q, c' ≠ c := by
      by_contra hno
      push_neg at hno
      have h1 := Set.ncard_le_ncard
        (fun z hz => Set.mem_singleton_iff.2 (hno z hz) : Q ⊆ {c}) (Set.finite_singleton c)
      rw [Set.ncard_singleton] at h1
      omega
    have hcC := hQC hcQ
    refine ⟨c, hcC.1, hcC.2, ?_, ?_⟩
    · intro Y hY hYr
      by_contra hbig
      have hYC : Y ⊆ M.E \ K := hY.trans Set.sdiff_subset
      have hYfin : Y.Finite := hCfin.subset hYC
      have hcY : c ∉ Y := fun hcY => (hY hcY).2 (mem_singleton c)
      by_cases hmeet : (Y ∩ Q).Nonempty
      · -- `Y` and `Q` lie in one point, which would contain `Y + c`
        obtain ⟨e, heY, heQ⟩ := hmeet
        have hYcl := subset_closure_singleton_of_le_one h (hYC.trans hCE) hYr heY
        have hQcl := subset_closure_singleton_of_le_one h (hQC.trans hCE) hQr heQ
        have hr : M.eRk (insert c Y) ≤ ((1 : ℕ) : ℕ∞) := by
          refine (M.eRk_mono (insert_subset (hQcl hcQ) hYcl)).trans ?_
          rw [M.eRk_closure_eq]
          exact_mod_cast M.eRk_singleton_le e
        have h1 := ncard_le_three_mul h (insert_subset (hCE hcC) (hYC.trans hCE)) hr
          (by norm_num)
        have h2 := Set.ncard_insert_of_notMem hcY hYfin
        omega
      · have hdisj : Disjoint Y Q :=
          Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hmeet)
        have h1 := Set.ncard_union_eq hdisj hYfin hQfin
        have h2 := Set.ncard_le_ncard (union_subset hYC hQC) hCfin
        omega
    · have hc'C0 : c' ∈ (M.E \ K) \ {c} :=
        ⟨hQC hc'Q, fun h' => hc'c (Set.mem_singleton_iff.1 h')⟩
      have hC0E : (M.E \ K) \ {c} ⊆ M.E := Set.sdiff_subset.trans hCE
      have hccl : c ∈ M.closure ((M.E \ K) \ {c}) :=
        M.closure_subset_closure (singleton_subset_iff.2 hc'C0)
          (subset_closure_singleton_of_le_one h (hQC.trans hCE) hQr hc'Q hcQ)
      intro z hz
      by_cases hzc : z = c
      · rw [hzc]
        exact hccl
      · exact M.subset_closure _ hC0E ⟨hz, fun h' => hzc (Set.mem_singleton_iff.1 h')⟩
  · -- no `3`-point inside `E - K`: `c` outside a basis of `E - K`
    push_neg at hQ
    obtain ⟨I, hI⟩ := M.exists_isBasis (M.E \ K) hCE
    obtain ⟨B, hB, hIB⟩ := hI.indep.exists_isBase_superset
    have hIn : I.ncard ≤ 4 := by
      have h1 := Set.ncard_le_ncard hIB (h.finite.subset hB.subset_ground)
      have h2 := base_ncard h hB
      omega
    have hnot : ¬ M.E \ K ⊆ I := fun hsub => by
      have := Set.ncard_le_ncard hsub (h.finite.subset hI.indep.subset_ground)
      omega
    obtain ⟨c, hcC, hcI⟩ := Set.not_subset.1 hnot
    refine ⟨c, hcC.1, hcC.2, fun Y hY hYr => ?_, ?_⟩
    · have := hQ Y (hY.trans Set.sdiff_subset) hYr
      omega
    · have hIC0 : I ⊆ (M.E \ K) \ {c} := fun z hz =>
        ⟨hI.subset hz, fun h' => hcI (by rw [← Set.mem_singleton_iff.1 h']; exact hz)⟩
      calc M.E \ K ⊆ M.closure (M.E \ K) := M.subset_closure _ hCE
        _ = M.closure I := hI.closure_eq_closure.symm
        _ ⊆ M.closure ((M.E \ K) \ {c}) := M.closure_subset_closure hIC0

/-- **The choice lemma at `k = 3`.** Let `Da`, `Db`, `De` be independent triples covering the
plane `K` (`9` elements), with `Da`, `Db` light, and let `c ∉ K` be as in `exists_c`. Then
`De + c` is deletable. -/
theorem deletable_of_choice (h : StrictT0 M 3) {K Da Db De : Set α} {c : α} (hKf : M.IsFlat K)
    (hKn : K.ncard = 9) (hDa : M.Indep Da) (hDb : M.Indep Db) (hDe : M.Indep De)
    (hDaK : Da ⊆ K) (hDbK : Db ⊆ K) (hDeK : De ⊆ K) (hDen : De.ncard = 3)
    (hcov : ∀ e ∈ K, e ∈ Da ∨ e ∈ Db ∨ e ∈ De) (hcE : c ∈ M.E) (hcK : c ∉ K)
    (hpt : ∀ Y ⊆ (M.E \ K) \ {c}, M.eRk Y ≤ 1 → Y.ncard ≤ 2)
    (hcl : M.E \ K ⊆ M.closure ((M.E \ K) \ {c})) (hstar : LightPair M K Da Db) :
    Deletable M 3 (insert c De) := by
  have hKE := hKf.subset_ground
  have hfin : ∀ {Y : Set α}, Y ⊆ M.E → Y.Finite := fun hY => h.finite.subset hY
  -- `De + c` is a basis
  have hclDe : M.closure De ⊆ K := (M.closure_subset_closure hDeK).trans_eq hKf.closure
  obtain ⟨hSind, hSn⟩ := indep_insert_ncard h hDe hcE (fun hc => hcK (hclDe hc))
  have hSbase := isBase_of_indep_ncard h hSind (by omega)
  -- `C = E - K` has `5` elements and `C₀ = C - c` has `4`
  have hCn := ncard_diff_nine h hKE hKn
  have hcC : c ∈ M.E \ K := ⟨hcE, hcK⟩
  have hC0n : ((M.E \ K) \ {c}).ncard = 4 := by
    have := Set.ncard_sdiff_singleton_add_one hcC (hfin Set.sdiff_subset)
    omega
  have hC0fin : ((M.E \ K) \ {c}).Finite := hfin (Set.sdiff_subset.trans Set.sdiff_subset)
  refine ⟨hSbase, fun X hX => ?_⟩
  have hXS : X ⊆ M.E \ insert c De := hX
  have hXE : X ⊆ M.E := hXS.trans Set.sdiff_subset
  have hXfin : X.Finite := hfin hXE
  rw [Matroid.restrict_eRk_eq M hXS]
  obtain ⟨j, hj, hj4⟩ := h.exists_eRk_eq X
  rw [← hXfin.cast_ncard_eq, hj]
  suffices hN : 4 * X.ncard ≤ (4 * 3 - 2) * j by exact_mod_cast hN
  -- the part of `X` in `K` lies in `Da ∪ Db`, the rest in `C₀`
  have hXK : X ∩ K ⊆ (Da ∩ (X ∩ K)) ∪ (Db ∩ (X ∩ K)) := by
    intro z hz
    rcases hcov z hz.2 with hza | hzb | hze
    · exact Or.inl ⟨hza, hz⟩
    · exact Or.inr ⟨hzb, hz⟩
    · exact absurd (mem_insert_of_mem c hze) (hXS hz.1).2
  have hXC : X \ K ⊆ (M.E \ K) \ {c} := by
    intro z hz
    refine ⟨⟨hXE hz.1, hz.2⟩, fun hzc => (hXS hz.1).2 ?_⟩
    rw [Set.mem_singleton_iff.1 hzc]
    exact mem_insert c De
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard X K hXfin
  have hXKle : (X ∩ K).ncard ≤ (Da ∩ (X ∩ K)).ncard + (Db ∩ (X ∩ K)).ncard :=
    (Set.ncard_le_ncard hXK (hfin (union_subset (inter_subset_left.trans (hDaK.trans hKE))
      (inter_subset_left.trans (hDbK.trans hKE))))).trans (Set.ncard_union_le _ _)
  have hw4 : (X \ K).ncard ≤ 4 := (Set.ncard_le_ncard hXC hC0fin).trans hC0n.le
  have hw1 : j ≤ 1 → (X \ K).ncard ≤ 2 := by
    intro hj1
    refine hpt (X \ K) hXC ?_
    have h1 : M.eRk (X \ K) ≤ (j : ℕ∞) := (M.eRk_mono Set.sdiff_subset).trans hj.le
    exact h1.trans (by exact_mod_cast hj1)
  by_cases hXsubK : X ⊆ K
  · -- `|X| ≤ 2j`
    have hw0 : (X \ K).ncard = 0 := by
      rw [Set.sdiff_eq_empty.2 hXsubK, Set.ncard_empty]
    have hu := indep_inter_ncard_le h hDa (Y := X ∩ K)
      ((M.eRk_mono inter_subset_left).trans hj.le)
    have hv := indep_inter_ncard_le h hDb (Y := X ∩ K)
      ((M.eRk_mono inter_subset_left).trans hj.le)
    interval_cases j <;> omega
  obtain ⟨i, hi, hij⟩ := exists_eRk_inter_flat_lt h hXE hKf hXsubK hj
  have hu := indep_inter_ncard_le h hDa (Y := X ∩ K) hi.le
  have hv := indep_inter_ncard_le h hDb (Y := X ∩ K) hi.le
  by_cases hw : (X \ K).ncard = 4
  · -- `X ⊇ C₀`, so `cl(X) ⊇ C`
    have hXCeq : X \ K = (M.E \ K) \ {c} :=
      Set.eq_of_subset_of_ncard_le hXC (by omega) hC0fin
    have hC0X : (M.E \ K) \ {c} ⊆ X := by
      rw [← hXCeq]
      exact Set.sdiff_subset
    have hCcl : M.E \ K ⊆ M.closure X := hcl.trans (M.closure_subset_closure hC0X)
    have hclE := M.closure_subset_ground X
    interval_cases j
    · omega
    · have := hw1 le_rfl
      omega
    · -- rank `2`: `cl(X)` has at most `6` elements, `5` of them outside `K`
      have hcl6 := ncard_le_three_mul h hclE (j := 2)
        (by rw [M.eRk_closure_eq]; exact_mod_cast hj.le) (by norm_num)
      have hdisj : Disjoint (X ∩ K) (M.E \ K) :=
        Set.disjoint_left.2 fun _ hz hz' => hz'.2 hz.2
      have hU := Set.ncard_union_eq hdisj (hfin (inter_subset_left.trans hXE))
        (hfin Set.sdiff_subset)
      have hle := Set.ncard_le_ncard
        (union_subset ((inter_subset_left : X ∩ K ⊆ X).trans (M.subset_closure X hXE)) hCcl)
        (hfin hclE)
      omega
    · -- rank `3`: `cl(X)` is a plane `≠ K` through `C`
      have hFr : M.eRk (M.closure X) = 3 := by
        rw [M.eRk_closure_eq]
        exact_mod_cast hj
      have hFK : M.closure X ≠ K := by
        intro hEq
        apply hcK
        rw [← hEq]
        exact hCcl hcC
      have hst := hstar (M.closure X) (M.isFlat_closure X) hFr hFK hCcl
      have hu' : (Da ∩ (X ∩ K)).ncard ≤ (M.closure X ∩ Da).ncard :=
        Set.ncard_le_ncard (fun z hz => ⟨M.subset_closure X hXE hz.2.1, hz.1⟩)
          (hfin (inter_subset_left.trans hclE))
      have hv' : (Db ∩ (X ∩ K)).ncard ≤ (M.closure X ∩ Db).ncard :=
        Set.ncard_le_ncard (fun z hz => ⟨M.subset_closure X hXE hz.2.1, hz.1⟩)
          (hfin (inter_subset_left.trans hclE))
      omega
    · omega
  · interval_cases j
    · omega
    · have := hw1 le_rfl
      omega
    · omega
    · omega
    · omega

/-- **The `9`-plane case** (formerly the certificate `hit14g`): with a `9`-plane, some basis is
deletable. -/
theorem hitG (h : StrictT0 M 3) {K : Set α} (hKf : M.IsFlat K) (hKr : M.eRk K = 3)
    (hKc : K.encard = ((3 * 3 : ℕ) : ℕ∞)) : ∃ S, Deletable M 3 S := by
  have hKE := hKf.subset_ground
  have hKfin : K.Finite := h.finite.subset hKE
  have hKn : K.ncard = 9 := by
    have := ncard_of_encard h hKE hKc
    omega
  have hK9 : K.encard = ((9 : ℕ) : ℕ∞) := by
    rw [← hKfin.cast_ncard_eq, hKn]
  -- an Edmonds partition of `K` into three bases of `M ↾ K`
  have hDenseK : UniformlyDenseRatio (M ↾ K) 3 1 := by
    intro X hX
    have hXK : X ⊆ K := hX
    have hXfin : X.Finite := hKfin.subset hXK
    rw [Matroid.restrict_eRk_eq M hXK]
    obtain ⟨j, hj, hj4⟩ := h.exists_eRk_eq X
    have hj3 : j ≤ 3 := by
      have h' := M.eRk_mono hXK
      rw [hj, hKr] at h'
      exact_mod_cast h'
    have hle := h.ncard_le (hXK.trans hKE) hj hj3
    rw [← hXfin.cast_ncard_eq, hj]
    have h1 : 1 * X.ncard ≤ 3 * j := by omega
    exact_mod_cast h1
  have hRankK : (M ↾ K).eRank = ((3 : ℕ) : ℕ∞) := by
    rw [← Matroid.eRk_ground, Matroid.restrict_ground_eq, Matroid.restrict_eRk_eq _ subset_rfl]
    exact hKr.trans (by norm_num)
  obtain ⟨P, hPbase, hPpart⟩ := VHT.edmonds_partition VHT.theorem_2_1 (M ↾ K) (k := 3) (n := 9)
    (r := 3) (by norm_num) hKfin hK9 hRankK (by norm_num) hDenseK
  have hPK : ∀ x, P x ⊆ K := fun x => (hPbase x).subset_ground
  have hPind : ∀ x, M.Indep (P x) := fun x =>
    (Matroid.restrict_indep_iff.1 (hPbase x).indep).1
  have hPn : ∀ x, (P x).ncard = 3 := fun x =>
    ncard_of_encard h ((hPK x).trans hKE) ((hPbase x).encard_eq_eRank.trans hRankK)
  have hPdisj : ∀ x y, x ≠ y → Disjoint (P x) (P y) := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro e hx hy
    obtain ⟨z, -, hz⟩ := hPpart e (hPK x hx)
    exact hxy ((hz x hx).trans (hz y hy).symm)
  have hPcov : ∀ e ∈ K, e ∈ P 0 ∨ e ∈ P 1 ∨ e ∈ P 2 := by
    intro e he
    obtain ⟨x, hx, -⟩ := hPpart e he
    fin_cases x
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  obtain ⟨c, hcE, hcK, hpt, hcl⟩ := exists_c h hKf hKn
  rcases light_pair h hKf hKr hKn (hPind 0) (hPind 1) (hPind 2) (hPK 0) (hPK 1) (hPK 2)
    (hPn 0) (hPn 1) (hPdisj 0 1 (by decide)) (hPdisj 0 2 (by decide))
    (hPdisj 1 2 (by decide)) with hl | hl | hl
  · exact ⟨_, deletable_of_choice h hKf hKn (hPind 0) (hPind 1) (hPind 2) (hPK 0) (hPK 1)
      (hPK 2) (hPn 2) hPcov hcE hcK hpt hcl hl⟩
  · refine ⟨_, deletable_of_choice h hKf hKn (hPind 0) (hPind 2) (hPind 1) (hPK 0) (hPK 2)
      (hPK 1) (hPn 1) ?_ hcE hcK hpt hcl hl⟩
    intro e he
    rcases hPcov e he with h0 | h1 | h2
    · exact Or.inl h0
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl h2)
  · refine ⟨_, deletable_of_choice h hKf hKn (hPind 1) (hPind 2) (hPind 0) (hPK 1) (hPK 2)
      (hPK 0) (hPn 0) ?_ hcE hcK hpt hcl hl⟩
    intro e he
    rcases hPcov e he with h0 | h1 | h2
    · exact Or.inr (Or.inr h0)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)

end HitThree
end Hitting
end HigherRankKUM

#print axioms HigherRankKUM.Hitting.HitThree.hitG
#print axioms HigherRankKUM.Hitting.HitThree.hitLine
