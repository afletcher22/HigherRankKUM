import Probe.Rank4.Hitting

/-!
# Lemma H: the hitting lemma with no `3k`-plane and no `2k`-line

Let `M` be strict with t=0 on `4k+2` elements (`StrictT0 M k`), `k ≥ 2`, with no `3k`-plane and
no `2k`-line. Then some basis meets every `k`-point and every `(3k-1)`-plane, so it meets the
demands (`lemmaH`).

Proof outline (paper proof in `docs/research-ledger/RANK4_EXTENSION_THEOREM.md`, "Lemma H").

* Profile: a set of rank `≤ 1`, `≤ 2`, `≤ 3` has at most `k`, `2k-1`, `3k` elements, and there
  are no loops.
* There is at most one `k`-point (`KPoint.eq`). Fix a *protected* set `T ⊆ S` of size `≤ 1`
  meeting every `k`-point: `T = {p}` for `p` in the `k`-point, or `T = ∅`.
* Two distinct `(3k-1)`-planes meet in at most `2k-1` elements, so a set missing both has at most
  `3` elements (`ncard_le_three`). Hence a basis misses at most one `(3k-1)`-plane.
* If `S` misses `F`, swap some `s ∈ S \ T` for some `x ∈ F \ cl(S - s)`. The swap fails only if
  some *blocker* `G ≠ F` misses `S - s`. Three elements with blockers are impossible
  (`not_three_blockers`): the lines `G_j ∩ F` have `≥ 2k-1` elements each, pairwise meet in
  `≤ k-1` elements, and would not fit in `F`.
-/

namespace HigherRankKUM
namespace Hitting

open Set
open scoped Matroid

namespace LemmaH

variable {α : Type*} {M : Matroid α} {k : ℕ}

/-! ### Generic helpers -/

/-- A superset of `X` of no larger rank lies in the closure of `X`. -/
theorem subset_closure_of_eRk_le (hfin : M.E.Finite) {X Y : Set α} (hXY : X ⊆ Y)
    (hY : Y ⊆ M.E) (hr : M.eRk Y ≤ M.eRk X) : Y ⊆ M.closure X := by
  have hXfin : X.Finite := hfin.subset (hXY.trans hY)
  rw [(M.isRkFinite_of_finite hXfin).closure_eq_closure_of_subset_of_eRk_ge_eRk hXY hr]
  exact M.subset_closure Y hY

/-- Inclusion–exclusion for three finite sets, dropping the triple intersection. -/
theorem ncard_add_add_le {A B C : Set α} (hA : A.Finite) (hB : B.Finite) (hC : C.Finite) :
    A.ncard + B.ncard + C.ncard ≤
      (A ∪ B ∪ C).ncard + (A ∩ B).ncard + (A ∩ C).ncard + (B ∩ C).ncard := by
  have h1 := Set.ncard_union_add_ncard_inter A B hA hB
  have h2 := Set.ncard_union_add_ncard_inter (A ∪ B) C (hA.union hB) hC
  have heq : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  have h3 := Set.ncard_union_le (A ∩ C) (B ∩ C)
  rw [← heq] at h3
  omega

/-! ### The profile -/

/-- No flat of rank `2` has exactly `2k` elements. -/
def NoTwoKLine (M : Matroid α) (k : ℕ) : Prop :=
  ∀ F, M.IsFlat F → M.eRk F = 2 → F.encard ≠ ((2 * k : ℕ) : ℕ∞)

theorem base_ncard (h : StrictT0 M k) {S : Set α} (hS : M.IsBase S) : S.ncard = 4 := by
  have hSfin : S.Finite := h.finite.subset hS.subset_ground
  have h4 : S.encard = (4 : ℕ∞) := by rw [hS.encard_eq_eRank, h.rank]
  rw [← hSfin.cast_ncard_eq] at h4
  exact_mod_cast h4

/-- No loops: a nonempty subset of the ground set has rank at least `1`. -/
theorem one_le_eRk (h : StrictT0 M k) {X : Set α} (hX : X ⊆ M.E) (hne : X.Nonempty) :
    1 ≤ M.eRk X := by
  obtain ⟨j, hj, -⟩ := h.exists_eRk_eq X
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have := h.four_mul_ncard_lt hX hne hj (by norm_num)
    omega
  · rw [hj]
    exact_mod_cast (show 1 ≤ j by omega)

theorem ncard_le_of_eRk_le_one (h : StrictT0 M k) {X : Set α} (hX : X ⊆ M.E)
    (hr : M.eRk X ≤ 1) : X.ncard ≤ k := by
  obtain ⟨j, hj, -⟩ := h.exists_eRk_eq X
  have hj1 : j ≤ 1 := by rw [hj] at hr; exact_mod_cast hr
  have := (h.ncard_le hX hj (by omega)).trans (Nat.mul_le_mul_right k hj1)
  omega

/-- With no `2k`-line, a set of rank at most `2` has at most `2k-1` elements. -/
theorem ncard_add_one_le_of_eRk_le_two (h : StrictT0 M k) (hk : 1 ≤ k) (h2 : NoTwoKLine M k)
    {X : Set α} (hX : X ⊆ M.E) (hr : M.eRk X ≤ 2) : X.ncard + 1 ≤ 2 * k := by
  obtain ⟨j, hj, -⟩ := h.exists_eRk_eq X
  have hj2 : j ≤ 2 := by rw [hj] at hr; exact_mod_cast hr
  have hle := h.ncard_le hX hj (by omega)
  interval_cases j
  · omega
  · omega
  · by_contra hbig
    have hclE := M.closure_subset_ground X
    have hclfin : (M.closure X).Finite := h.finite.subset hclE
    have hcl1 := h.ncard_le hclE (j := 2) (by rw [M.eRk_closure_eq]; exact_mod_cast hj)
      (by norm_num)
    have hcl2 := Set.ncard_le_ncard (M.subset_closure X hX) hclfin
    apply h2 (M.closure X) (M.isFlat_closure X) (by rw [M.eRk_closure_eq]; exact_mod_cast hj)
    rw [← hclfin.cast_ncard_eq]
    exact_mod_cast (show (M.closure X).ncard = 2 * k by omega)

theorem ncard_le_of_eRk_le_three (h : StrictT0 M k) {X : Set α} (hX : X ⊆ M.E)
    (hr : M.eRk X ≤ 3) : X.ncard ≤ 3 * k := by
  obtain ⟨j, hj, -⟩ := h.exists_eRk_eq X
  have hj3 : j ≤ 3 := by rw [hj] at hr; exact_mod_cast hr
  exact (h.ncard_le hX hj hj3).trans (Nat.mul_le_mul_right k hj3)

/-! ### `k`-points -/

/-- A `k`-point: a flat of rank `1` with `k` elements. -/
def KPoint (M : Matroid α) (k : ℕ) (P : Set α) : Prop :=
  M.IsFlat P ∧ M.eRk P = 1 ∧ P.encard = (k : ℕ∞)

theorem KPoint.ncard {P : Set α} (hP : KPoint M k P) (h : StrictT0 M k) : P.ncard = k := by
  have hPfin : P.Finite := h.finite.subset hP.1.subset_ground
  have hc := hP.2.2
  rw [← hPfin.cast_ncard_eq] at hc
  exact_mod_cast hc

/-- A `k`-point is the closure of each of its elements. -/
theorem KPoint.closure_singleton {P : Set α} (hP : KPoint M k P) (h : StrictT0 M k) {e : α}
    (he : e ∈ P) : M.closure {e} = P := by
  have heE : e ∈ M.E := hP.1.subset_ground he
  apply Set.Subset.antisymm
    ((M.closure_subset_closure (singleton_subset_iff.2 he)).trans_eq hP.1.closure)
  refine subset_closure_of_eRk_le h.finite (singleton_subset_iff.2 he) hP.1.subset_ground ?_
  rw [hP.2.1]
  exact one_le_eRk h (singleton_subset_iff.2 heE) (singleton_nonempty e)

/-- **Step 1.** There is at most one `k`-point. -/
theorem KPoint.eq (h : StrictT0 M k) (hk : 1 ≤ k) (h2 : NoTwoKLine M k) {P Q : Set α}
    (hP : KPoint M k P) (hQ : KPoint M k Q) : P = Q := by
  have hPE := hP.1.subset_ground
  have hQE := hQ.1.subset_ground
  have hPfin : P.Finite := h.finite.subset hPE
  have hQfin : Q.Finite := h.finite.subset hQE
  have hr : M.eRk (P ∪ Q) ≤ 2 := by
    refine (M.eRk_union_le_eRk_add_eRk P Q).trans ?_
    rw [hP.2.1, hQ.2.1]
    exact one_add_one_eq_two.le
  have hU := ncard_add_one_le_of_eRk_le_two h hk h2 (union_subset hPE hQE) hr
  have hUI := Set.ncard_union_add_ncard_inter P Q hPfin hQfin
  have hPc := hP.ncard h
  have hQc := hQ.ncard h
  obtain ⟨e, heP, heQ⟩ : (P ∩ Q).Nonempty :=
    (Set.ncard_pos (hPfin.subset inter_subset_left)).1 (by omega)
  exact (hP.closure_singleton h heP).symm.trans (hQ.closure_singleton h heQ)

/-- If every `k`-point meets `T ⊆ S` and the flat `F` misses `S`, then a set of rank at most `1`
inside `F` has at most `k-1` elements. -/
theorem ncard_add_one_le_of_subset_of_eRk_le_one (h : StrictT0 M k) {S T F Y : Set α}
    (hT : ∀ Q, KPoint M k Q → (Q ∩ T).Nonempty) (hTS : T ⊆ S) (hF : M.IsFlat F)
    (hFS : Disjoint F S) (hY : Y ⊆ F) (hr : M.eRk Y ≤ 1) : Y.ncard + 1 ≤ k := by
  have hYE : Y ⊆ M.E := hY.trans hF.subset_ground
  have hle := ncard_le_of_eRk_le_one h hYE hr
  by_contra hbig
  have hne : Y.Nonempty := (Set.ncard_pos (h.finite.subset hYE)).1 (by omega)
  have hr1 : M.eRk Y = 1 := le_antisymm hr (one_le_eRk h hYE hne)
  have hclE := M.closure_subset_ground Y
  have hclfin : (M.closure Y).Finite := h.finite.subset hclE
  have hclF : M.closure Y ⊆ F := (M.closure_subset_closure hY).trans_eq hF.closure
  have hcl1 := ncard_le_of_eRk_le_one h hclE ((M.eRk_closure_eq Y).trans_le hr)
  have hcl2 := Set.ncard_le_ncard (M.subset_closure Y hYE) hclfin
  have hQ : KPoint M k (M.closure Y) := by
    refine ⟨M.isFlat_closure Y, (M.eRk_closure_eq Y).trans hr1, ?_⟩
    rw [← hclfin.cast_ncard_eq]
    exact_mod_cast (show (M.closure Y).ncard = k by omega)
  obtain ⟨q, hqQ, hqT⟩ := hT _ hQ
  exact Set.disjoint_left.1 hFS (hclF hqQ) (hTS hqT)

/-! ### `(3k-1)`-planes -/

/-- A `(3k-1)`-plane: a flat of rank `3` with `3k-1` elements. -/
def BigPlane (M : Matroid α) (k : ℕ) (F : Set α) : Prop :=
  M.IsFlat F ∧ M.eRk F = 3 ∧ F.encard = ((3 * k - 1 : ℕ) : ℕ∞)

theorem BigPlane.ncard {F : Set α} (hF : BigPlane M k F) (h : StrictT0 M k) :
    F.ncard = 3 * k - 1 := by
  have hFfin : F.Finite := h.finite.subset hF.1.subset_ground
  have hc := hF.2.2
  rw [← hFfin.cast_ncard_eq] at hc
  exact_mod_cast hc

/-- Two distinct `(3k-1)`-planes meet in a set of rank at most `2`. -/
theorem BigPlane.eRk_inter_le_two (h : StrictT0 M k) {F G : Set α} (hF : BigPlane M k F)
    (hG : BigPlane M k G) (hne : F ≠ G) : M.eRk (F ∩ G) ≤ 2 := by
  obtain ⟨j, hj, -⟩ := h.exists_eRk_eq (F ∩ G)
  rw [hj]
  by_contra hj2
  have hj3 : 3 ≤ j := by
    by_contra hlt
    exact hj2 (by exact_mod_cast (show j ≤ 2 by omega))
  have hge : ∀ {Z : Set α}, M.eRk Z = 3 → M.eRk Z ≤ M.eRk (F ∩ G) := fun hZ => by
    rw [hZ, hj]
    exact_mod_cast hj3
  have hFG : F ⊆ G :=
    (subset_closure_of_eRk_le h.finite inter_subset_left hF.1.subset_ground (hge hF.2.1)).trans
      ((M.closure_subset_closure inter_subset_right).trans_eq hG.1.closure)
  have hGF : G ⊆ F :=
    (subset_closure_of_eRk_le h.finite inter_subset_right hG.1.subset_ground (hge hG.2.1)).trans
      ((M.closure_subset_closure inter_subset_left).trans_eq hF.1.closure)
  exact hne (Set.Subset.antisymm hFG hGF)

/-- **Step 2.** Two distinct `(3k-1)`-planes share at most `2k-1` elements. -/
theorem BigPlane.ncard_inter (h : StrictT0 M k) (hk : 1 ≤ k) (h2 : NoTwoKLine M k)
    {F G : Set α} (hF : BigPlane M k F) (hG : BigPlane M k G) (hne : F ≠ G) :
    (F ∩ G).ncard + 1 ≤ 2 * k :=
  ncard_add_one_le_of_eRk_le_two h hk h2 (inter_subset_left.trans hF.1.subset_ground)
    (hF.eRk_inter_le_two h hG hne)

/-- **Step 2.** A set that misses two distinct `(3k-1)`-planes has at most `3` elements. In
particular a basis misses at most one `(3k-1)`-plane. -/
theorem ncard_le_three (h : StrictT0 M k) (hk : 1 ≤ k) (h2 : NoTwoKLine M k)
    {F G A : Set α} (hF : BigPlane M k F) (hG : BigPlane M k G) (hne : F ≠ G) (hA : A ⊆ M.E)
    (hAF : Disjoint A F) (hAG : Disjoint A G) : A.ncard ≤ 3 := by
  have hFE := hF.1.subset_ground
  have hGE := hG.1.subset_ground
  have hFfin : F.Finite := h.finite.subset hFE
  have hGfin : G.Finite := h.finite.subset hGE
  have hI := hF.ncard_inter h hk h2 hG hne
  have hU := Set.ncard_union_add_ncard_inter F G hFfin hGfin
  have hAU := Set.ncard_union_eq (Set.disjoint_union_right.2 ⟨hAF, hAG⟩)
    (h.finite.subset hA) (hFfin.union hGfin)
  have hle := Set.ncard_le_ncard (union_subset hA (union_subset hFE hGE)) h.finite
  have hEc := h.ncard_ground
  have hFc := hF.ncard h
  have hGc := hG.ncard h
  omega

/-! ### The swap -/

/-- The flat `F` and the basis `S` do not cover the ground set. -/
theorem exists_outside (h : StrictT0 M k) (hk : 2 ≤ k) {F S : Set α} (hF : BigPlane M k F)
    (hS : M.IsBase S) : ∃ d ∈ M.E, d ∉ F ∧ d ∉ S := by
  have hFfin : F.Finite := h.finite.subset hF.1.subset_ground
  have hSfin : S.Finite := h.finite.subset hS.subset_ground
  have hnot : ¬ M.E ⊆ F ∪ S := fun hsub => by
    have h1 := Set.ncard_le_ncard hsub (hFfin.union hSfin)
    have h2 := Set.ncard_union_le F S
    have := hF.ncard h
    have := base_ncard h hS
    have := h.ncard_ground
    omega
  obtain ⟨d, hdE, hd⟩ := Set.not_subset.1 hnot
  exact ⟨d, hdE, fun hdF => hd (Or.inl hdF), fun hdS => hd (Or.inr hdS)⟩

/-- **Step 3.** If `S` misses `F`, then `F ⊄ cl(S - s)`. -/
theorem exists_mem_not_closure (h : StrictT0 M k) {F S : Set α} (hF : BigPlane M k F)
    (hS : M.IsBase S) (hFS : Disjoint F S) {s : α} (hs : s ∈ S) :
    ∃ x ∈ F, x ∉ M.closure (S \ {s}) := by
  have hSfin : S.Finite := h.finite.subset hS.subset_ground
  have hS'E : S \ {s} ⊆ M.E := Set.sdiff_subset.trans hS.subset_ground
  have hS'fin : (S \ {s}).Finite := hSfin.subset Set.sdiff_subset
  have hS'card := Set.ncard_sdiff_singleton_add_one hs hSfin
  have hScard := base_ncard h hS
  by_contra hc
  have hcl : F ⊆ M.closure (S \ {s}) := by
    intro x hx
    by_contra hx'
    exact hc ⟨x, hx, hx'⟩
  have hsub : F ∪ (S \ {s}) ⊆ M.closure (S \ {s}) := union_subset hcl (M.subset_closure _ hS'E)
  have hr : M.eRk (F ∪ (S \ {s})) ≤ 3 := by
    refine (M.eRk_mono hsub).trans ?_
    rw [M.eRk_closure_eq]
    refine (M.eRk_le_encard _).trans ?_
    rw [← hS'fin.cast_ncard_eq]
    exact_mod_cast (show (S \ {s}).ncard ≤ 3 by omega)
  have hle := ncard_le_of_eRk_le_three h (union_subset hF.1.subset_ground hS'E) hr
  have hdisj : Disjoint F (S \ {s}) := hFS.mono_right Set.sdiff_subset
  have hU := Set.ncard_union_eq hdisj (h.finite.subset hF.1.subset_ground) hS'fin
  have := hF.ncard h
  omega

/-- `G` blocks the swap at `s`: a `(3k-1)`-plane other than `F` that misses `S - s`. -/
def Blocker (M : Matroid α) (k : ℕ) (F S G : Set α) (s : α) : Prop :=
  BigPlane M k G ∧ G ≠ F ∧ Disjoint G (S \ {s})

section Blocker

variable {F S G : Set α} {s : α}

/-- **Step 4.** A blocker for `s` contains `s`. -/
theorem Blocker.mem (h : StrictT0 M k) (hk : 1 ≤ k) (h2 : NoTwoKLine M k)
    (hF : BigPlane M k F) (hS : M.IsBase S) (hFS : Disjoint F S) (hG : Blocker M k F S G s) :
    s ∈ G := by
  by_contra hsG
  have hSG : Disjoint S G := by
    rw [Set.disjoint_left]
    intro y hyS hyG
    by_cases hys : y = s
    · exact hsG (by rw [← hys]; exact hyG)
    · exact Set.disjoint_left.1 hG.2.2 hyG ⟨hyS, hys⟩
  have := ncard_le_three h hk h2 hF hG.1 hG.2.1.symm hS.subset_ground hFS.symm hSG
  have := base_ncard h hS
  omega

/-- **Step 4.** A blocker for `s` contains every element outside `F ∪ S`. -/
theorem Blocker.mem_of_outside (h : StrictT0 M k) (hk : 1 ≤ k) (h2 : NoTwoKLine M k)
    (hF : BigPlane M k F) (hS : M.IsBase S) (hFS : Disjoint F S) (hG : Blocker M k F S G s)
    (hs : s ∈ S) {d : α} (hdE : d ∈ M.E) (hdF : d ∉ F) (hdS : d ∉ S) : d ∈ G := by
  by_contra hdG
  have hSfin : S.Finite := h.finite.subset hS.subset_ground
  have hAE : insert d (S \ {s}) ⊆ M.E :=
    insert_subset hdE (Set.sdiff_subset.trans hS.subset_ground)
  have hAF : Disjoint (insert d (S \ {s})) F := by
    rw [Set.disjoint_left]
    rintro y (rfl | hy) hyF
    · exact hdF hyF
    · exact Set.disjoint_left.1 hFS hyF hy.1
  have hAG : Disjoint (insert d (S \ {s})) G := by
    rw [Set.disjoint_left]
    rintro y (rfl | hy) hyG
    · exact hdG hyG
    · exact Set.disjoint_left.1 hG.2.2 hyG hy
  have hle := ncard_le_three h hk h2 hF hG.1 hG.2.1.symm hAE hAF hAG
  have hS'fin : (S \ {s}).Finite := hSfin.subset Set.sdiff_subset
  have hdS' : d ∉ S \ {s} := fun hd => hdS hd.1
  have h1 : (insert d (S \ {s})).ncard = (S \ {s}).ncard + 1 :=
    Set.ncard_insert_of_notMem hdS' hS'fin
  have h1' := Set.ncard_sdiff_singleton_add_one hs hSfin
  have := base_ncard h hS
  omega

/-- **Step 5.** A blocker `G` for `s` meets `F` in at least `2k-1` elements. -/
theorem Blocker.le_ncard_inter (h : StrictT0 M k) (hF : BigPlane M k F) (hS : M.IsBase S)
    (hFS : Disjoint F S) (hG : Blocker M k F S G s) (hs : s ∈ S) :
    2 * k ≤ (G ∩ F).ncard + 1 := by
  have hFE := hF.1.subset_ground
  have hGE := hG.1.1.subset_ground
  have hSE := hS.subset_ground
  have hSfin : S.Finite := h.finite.subset hSE
  have hdisj : Disjoint (G \ F) (F ∪ (S \ {s})) := by
    rw [Set.disjoint_left]
    rintro y ⟨hyG, hyF⟩ (hyF' | hyS)
    · exact hyF hyF'
    · exact Set.disjoint_left.1 hG.2.2 hyG hyS
  have hsub : (G \ F) ∪ (F ∪ (S \ {s})) ⊆ M.E :=
    union_subset (Set.sdiff_subset.trans hGE) (union_subset hFE (Set.sdiff_subset.trans hSE))
  have hGFfin : (G \ F).Finite := h.finite.subset (Set.sdiff_subset.trans hGE)
  have hFfin : F.Finite := h.finite.subset hFE
  have hS'fin : (S \ {s}).Finite := hSfin.subset Set.sdiff_subset
  have hFS' : Disjoint F (S \ {s}) := hFS.mono_right Set.sdiff_subset
  have h1 := Set.ncard_le_ncard hsub h.finite
  have h2 := Set.ncard_union_eq hdisj hGFfin (hFfin.union hS'fin)
  have h3 := Set.ncard_union_eq hFS' hFfin hS'fin
  have h4 := Set.ncard_inter_add_ncard_sdiff_eq_ncard G F (h.finite.subset hGE)
  have h5 := Set.ncard_sdiff_singleton_add_one hs hSfin
  have := base_ncard h hS
  have := hF.ncard h
  have := hG.1.ncard h
  have := h.ncard_ground
  omega

end Blocker

/-- **Step 5.** Blockers `Ga`, `Gb` for distinct `a`, `b` meet inside `F` in at most `k-1`
elements. -/
theorem Blocker.ncard_inter_inter (h : StrictT0 M k) (hk : 1 ≤ k) (h2 : NoTwoKLine M k)
    {F S : Set α} (hF : BigPlane M k F) (hS : M.IsBase S) (hFS : Disjoint F S)
    (hpt : ∀ Y ⊆ F, M.eRk Y ≤ 1 → Y.ncard + 1 ≤ k)
    {d : α} (hdE : d ∈ M.E) (hdF : d ∉ F) (hdS : d ∉ S)
    {Ga Gb : Set α} {a b : α} (hGa : Blocker M k F S Ga a) (hGb : Blocker M k F S Gb b)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ((Ga ∩ F) ∩ (Gb ∩ F)).ncard + 1 ≤ k := by
  have hne : Ga ≠ Gb := by
    intro hEq
    have haGa := hGa.mem h hk h2 hF hS hFS
    rw [hEq] at haGa
    exact Set.disjoint_left.1 hGb.2.2 haGa ⟨ha, hab⟩
  have hYF : (Ga ∩ F) ∩ (Gb ∩ F) ⊆ F := fun x hx => hx.1.2
  have hYG : (Ga ∩ F) ∩ (Gb ∩ F) ⊆ Ga ∩ Gb := fun x hx => ⟨hx.1.1, hx.2.1⟩
  have hGE : Ga ∩ Gb ⊆ M.E := inter_subset_left.trans hGa.1.1.subset_ground
  refine hpt _ hYF ?_
  have hdGa := hGa.mem_of_outside h hk h2 hF hS hFS ha hdE hdF hdS
  have hdGb := hGb.mem_of_outside h hk h2 hF hS hFS hb hdE hdF hdS
  obtain ⟨j, hj, -⟩ := h.exists_eRk_eq ((Ga ∩ F) ∩ (Gb ∩ F))
  rw [hj]
  by_contra hj1
  have hj2 : 2 ≤ j := by
    by_contra hlt
    exact hj1 (by exact_mod_cast (show j ≤ 1 by omega))
  have hge : M.eRk (Ga ∩ Gb) ≤ M.eRk ((Ga ∩ F) ∩ (Gb ∩ F)) := by
    rw [hj]
    exact (hGa.1.eRk_inter_le_two h hGb.1 hne).trans (by exact_mod_cast hj2)
  have hsub := subset_closure_of_eRk_le h.finite hYG hGE hge
  have hclF : M.closure ((Ga ∩ F) ∩ (Gb ∩ F)) ⊆ F :=
    (M.closure_subset_closure hYF).trans_eq hF.1.closure
  exact hdF (hclF (hsub ⟨hdGa, hdGb⟩))

/-- **Step 5.** Three distinct elements of `S` cannot all have blockers. -/
theorem not_three_blockers (h : StrictT0 M k) (hk : 2 ≤ k) (h2 : NoTwoKLine M k)
    {F S : Set α} (hF : BigPlane M k F) (hS : M.IsBase S) (hFS : Disjoint F S)
    (hpt : ∀ Y ⊆ F, M.eRk Y ≤ 1 → Y.ncard + 1 ≤ k)
    {a b c : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {Ga Gb Gc : Set α} (hGa : Blocker M k F S Ga a)
    (hGb : Blocker M k F S Gb b) (hGc : Blocker M k F S Gc c) : False := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨d, hdE, hdF, hdS⟩ := exists_outside h hk hF hS
  have la := hGa.le_ncard_inter h hF hS hFS ha
  have lb := hGb.le_ncard_inter h hF hS hFS hb
  have lc := hGc.le_ncard_inter h hF hS hFS hc
  have iab := Blocker.ncard_inter_inter h hk1 h2 hF hS hFS hpt hdE hdF hdS hGa hGb ha hb hab
  have iac := Blocker.ncard_inter_inter h hk1 h2 hF hS hFS hpt hdE hdF hdS hGa hGc ha hc hac
  have ibc := Blocker.ncard_inter_inter h hk1 h2 hF hS hFS hpt hdE hdF hdS hGb hGc hb hc hbc
  have hFfin : F.Finite := h.finite.subset hF.1.subset_ground
  have hcount := ncard_add_add_le (hFfin.subset (inter_subset_right : Ga ∩ F ⊆ F))
    (hFfin.subset (inter_subset_right : Gb ∩ F ⊆ F))
    (hFfin.subset (inter_subset_right : Gc ∩ F ⊆ F))
  have hU : ((Ga ∩ F) ∪ (Gb ∩ F) ∪ (Gc ∩ F)).ncard ≤ F.ncard :=
    Set.ncard_le_ncard
      (union_subset (union_subset inter_subset_right inter_subset_right) inter_subset_right) hFfin
  have := hF.ncard h
  omega

/-- **Steps 4–5.** Some `s ∈ S \ T` has no blocker. -/
theorem exists_unblocked (h : StrictT0 M k) (hk : 2 ≤ k) (h2 : NoTwoKLine M k)
    {S T F : Set α} (hS : M.IsBase S) (hTS : T ⊆ S) (hT1 : T.ncard ≤ 1)
    (hT : ∀ Q, KPoint M k Q → (Q ∩ T).Nonempty) (hF : BigPlane M k F) (hFS : Disjoint F S) :
    ∃ s ∈ S, s ∉ T ∧ ∀ G, BigPlane M k G → G ≠ F → (G ∩ (S \ {s})).Nonempty := by
  by_contra hc
  have hblock : ∀ s ∈ S \ T, ∃ G, Blocker M k F S G s := by
    intro s hs
    by_contra hno
    apply hc
    refine ⟨s, hs.1, hs.2, fun G hG hGF => ?_⟩
    by_contra hne
    exact hno ⟨G, hG, hGF,
      Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne)⟩
  have hSfin : S.Finite := h.finite.subset hS.subset_ground
  have hScard := base_ncard h hS
  have hST := Set.ncard_sdiff_add_ncard_of_subset hTS hSfin
  have hSTfin : (S \ T).Finite := hSfin.subset Set.sdiff_subset
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ :=
    (Set.two_lt_ncard hSTfin).1 (show 2 < (S \ T).ncard by omega)
  obtain ⟨Ga, hGa⟩ := hblock a ha
  obtain ⟨Gb, hGb⟩ := hblock b hb
  obtain ⟨Gc, hGc⟩ := hblock c hc'
  have hpt : ∀ Y ⊆ F, M.eRk Y ≤ 1 → Y.ncard + 1 ≤ k := fun Y hY hr =>
    ncard_add_one_le_of_subset_of_eRk_le_one h hT hTS hF.1 hFS hY hr
  exact not_three_blockers h hk h2 hF hS hFS hpt ha.1 hb.1 hc'.1 hab hac hbc hGa hGb hGc

/-- **The swap.** Given a basis `S` and a protected set `T ⊆ S` of size at most `1`, some basis
containing `T` meets every `(3k-1)`-plane. -/
theorem exists_isBase_meets_bigPlanes (h : StrictT0 M k) (hk : 2 ≤ k) (h2 : NoTwoKLine M k)
    {S T : Set α} (hS : M.IsBase S) (hTS : T ⊆ S) (hT1 : T.ncard ≤ 1)
    (hT : ∀ Q, KPoint M k Q → (Q ∩ T).Nonempty) :
    ∃ S', M.IsBase S' ∧ T ⊆ S' ∧ ∀ F, BigPlane M k F → (F ∩ S').Nonempty := by
  by_cases hall : ∀ F, BigPlane M k F → (F ∩ S).Nonempty
  · exact ⟨S, hS, hTS, hall⟩
  obtain ⟨F, hF, hFS⟩ : ∃ F, BigPlane M k F ∧ Disjoint F S := by
    by_contra hc
    apply hall
    intro F hF
    by_contra hne
    exact hc ⟨F, hF, Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne)⟩
  obtain ⟨s, hsS, hsT, hgood⟩ := exists_unblocked h hk h2 hS hTS hT1 hT hF hFS
  obtain ⟨x, hxF, hxcl⟩ := exists_mem_not_closure h hF hS hFS hsS
  have hxS : x ∉ S := fun hxS => Set.disjoint_left.1 hFS hxF hxS
  have hxS' : x ∉ S \ {s} := fun hx => hxS hx.1
  have hI : M.Indep (S \ {s}) := hS.indep.subset Set.sdiff_subset
  have hind : M.Indep (insert x (S \ {s})) :=
    (hI.insert_indep_iff_of_notMem hxS').2 ⟨hF.1.subset_ground hxF, hxcl⟩
  have hTS' : T ⊆ insert x (S \ {s}) := by
    intro t ht
    refine mem_insert_of_mem _ ⟨hTS ht, fun hts => hsT ?_⟩
    rw [← Set.mem_singleton_iff.1 hts]
    exact ht
  refine ⟨insert x (S \ {s}), hS.exchange_isBase_of_indep hxS hind, hTS', fun G hG => ?_⟩
  by_cases hGF : G = F
  · rw [hGF]
    exact ⟨x, hxF, mem_insert x _⟩
  · obtain ⟨y, hyG, hyS⟩ := hgood G hG hGF
    exact ⟨y, hyG, mem_insert_of_mem _ hyS⟩

/-- A basis `S` and a protected set `T ⊆ S` of size at most `1` meeting every `k`-point. -/
theorem exists_protected (h : StrictT0 M k) (hk : 1 ≤ k) (h2 : NoTwoKLine M k) :
    ∃ S T : Set α, M.IsBase S ∧ T ⊆ S ∧ T.ncard ≤ 1 ∧
      ∀ Q, KPoint M k Q → (Q ∩ T).Nonempty := by
  by_cases hP : ∃ P, KPoint M k P
  · obtain ⟨P, hP⟩ := hP
    have hPfin : P.Finite := h.finite.subset hP.1.subset_ground
    obtain ⟨p, hp⟩ : P.Nonempty := (Set.ncard_pos hPfin).1 (by rw [hP.ncard h]; omega)
    have hpE : p ∈ M.E := hP.1.subset_ground hp
    have hpnl : M.IsNonloop p := Matroid.eRk_singleton_eq_one_iff.1
      (le_antisymm (M.eRk_singleton_le p)
        (one_le_eRk h (singleton_subset_iff.2 hpE) (singleton_nonempty p)))
    obtain ⟨S, hS, hpS⟩ := hpnl.exists_mem_isBase
    refine ⟨S, {p}, hS, singleton_subset_iff.2 hpS, by simp, fun Q hQ => ⟨p, ?_, mem_singleton p⟩⟩
    rw [KPoint.eq h hk h2 hQ hP]
    exact hp
  · obtain ⟨S, hS⟩ := M.exists_isBase
    exact ⟨S, ∅, hS, empty_subset S, by simp, fun Q hQ => (hP ⟨Q, hQ⟩).elim⟩

end LemmaH

/-- **Lemma H** (hitting lemma, reduced case): with no `3k`-plane and no `2k`-line, some basis
meets the demands. -/
theorem lemmaH {α : Type*} : LemmaHStatement α := by
  intro M k hk h h3 h2
  obtain ⟨S, T, hS, hTS, hT1, hT⟩ := LemmaH.exists_protected h (by omega) h2
  obtain ⟨S', hS', hTS', hbig⟩ := LemmaH.exists_isBase_meets_bigPlanes h hk h2 hS hTS hT1 hT
  refine ⟨S', hS', ?_, ?_, ?_, ?_⟩
  · intro F hF1 hF2 hF3
    obtain ⟨x, hxF, hxT⟩ := hT F ⟨hF1, hF2, hF3⟩
    exact ⟨x, hxF, hTS' hxT⟩
  · intro F hF hr he
    exact absurd he (h2 F hF hr)
  · intro F hF hr he
    exact absurd he (h3 F hF hr)
  · intro F hF1 hF2 hF3
    exact hbig F ⟨hF1, hF2, hF3⟩

end Hitting
end HigherRankKUM

#print axioms HigherRankKUM.Hitting.lemmaH
