import HigherRankKUM.Rank4.LemmaH
import HigherRankKUM.VHT.Covers
import HigherRankKUM.VHT.Theorem21

/-!
# The hitting lemma with a dangerous plane

Let `M` be a strict rank-4 matroid on `4k+2` elements, `k ≥ 3` (`Strict4 M k`): no loops, points
have at most `k` elements, lines `2k`, planes `3k+1`. A *dangerous plane* is a plane `P` with
`3k+1` elements. This file shows that such an `M` has a deletable basis (`hitDanger`): a basis
`S` with `M \ S` uniformly dense, so at most `k-1`, `2k-1`, `3k-2` elements of `M \ S` on every
point, line, plane. With it, the strict `4k+2` case with a dangerous plane goes through the same
deletion step as the `t = 0` case, and needs no rank-3 input.

## Proof

Let `C = E - P`, which has `k+1` elements.

* Some `e₀ ∈ P` lies on no `k`-point: four disjoint `k`-points do not fit in `P`
  (`exists_light_elem`). By Edmonds, `P - e₀` splits into `k` independent triples `D x`.
* By counting over the triples (`sum_inter_eq`), every triple meets every `k`-point and every
  `2k`-line of `P`; so a rank-1 (rank-2) subset of `P - D x` has at most `k-1` (`2k-1`) elements.
* Choose `c ∈ C` (`exists_c`): in the `k`-point of `C` if there is one, else outside a basis of
  `C`, else anywhere if `C` is independent. Then every point of `C₀ = C - c` has at most `k-1`
  elements. Two distinct planes through `C₀` meet `P` inside one set `Q₀` of at most `k-1`
  elements (`cl(C) ∩ P`); if `C` is independent there are no two such planes.
* A plane `F ≠ P` through `C₀` with `|F ∩ P - D x| ≥ 2k-1` is *bad* for `x`. A plane is bad for at
  most one triple (`not_two_bad`), and there are at most two planes through `C₀` that can be bad
  (`not_three_planes`: three would need `(2k-1) + k + k > 3k+1` elements of `P`). With `k ≥ 3`
  triples, some `D x` has no bad plane (`exists_good_triple`).
* Then `D x + c` is deletable (`deletable_of_danger`), by a rank-by-rank count of `X ⊆ E - S`:
  its part in `P` lies in `P - D x`, the rest in `C₀`, and only `X ⊇ C₀` at rank 3 needs the
  choice of `x`.
-/

namespace HigherRankKUM
namespace Hitting

open Set LemmaH
open scoped Matroid

variable {α : Type*} {M : Matroid α} {k : ℕ}

/-- A strict rank-4 matroid on `4k+2` elements. Unlike `StrictT0`, dangerous planes are
allowed. -/
structure Strict4 (M : Matroid α) (k : ℕ) : Prop where
  finite : M.E.Finite
  rank : M.eRank = (4 : ℕ∞)
  card : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞)
  strict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4

namespace Strict4

theorem exists_eRk_eq (h : Strict4 M k) (X : Set α) : ∃ j : ℕ, M.eRk X = j ∧ j ≤ 4 := by
  have hle : M.eRk X ≤ (4 : ℕ∞) := by
    rw [← h.rank]
    exact M.eRk_le_eRank X
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hle
  exact ⟨j, hj, by exact_mod_cast hjle⟩

theorem ncard_ground (h : Strict4 M k) : M.E.ncard = 4 * k + 2 := by
  have h' := h.card
  rw [← h.finite.cast_ncard_eq] at h'
  exact_mod_cast h'

/-- Strict density for a nonempty set of rank at most `3`. -/
theorem four_mul_ncard_lt (h : Strict4 M k) {X : Set α} (hX : X ⊆ M.E) (hne : X.Nonempty)
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

/-- The strict profile, uniformly: `4|X| < (4k+2) j` for `X` of rank at most `j ≤ 3`, unless
`X` is empty. -/
theorem ncard_lt (h : Strict4 M k) {X : Set α} (hX : X ⊆ M.E) {j : ℕ} (hr : M.eRk X ≤ j)
    (hj : j ≤ 3) : 4 * X.ncard < (4 * k + 2) * j ∨ X.ncard = 0 := by
  obtain ⟨i, hi, -⟩ := h.exists_eRk_eq X
  have hij : i ≤ j := by
    rw [hi] at hr
    exact_mod_cast hr
  rcases X.eq_empty_or_nonempty with rfl | hne
  · right
    simp
  left
  have hlt := h.four_mul_ncard_lt hX hne hi (by omega)
  have hmul : (4 * k + 2) * i ≤ (4 * k + 2) * j := Nat.mul_le_mul_left _ hij
  omega

/-- No loops. -/
theorem one_le_eRk (h : Strict4 M k) {X : Set α} (hX : X ⊆ M.E) (hne : X.Nonempty) :
    1 ≤ M.eRk X := by
  obtain ⟨j, hj, -⟩ := h.exists_eRk_eq X
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have := h.four_mul_ncard_lt hX hne hj (by norm_num)
    omega
  · rw [hj]
    exact_mod_cast (show 1 ≤ j by omega)

/-- A set of rank at most `1` has at most `k` elements. -/
theorem ncard_le_pt (h : Strict4 M k) {X : Set α} (hX : X ⊆ M.E) (hr : M.eRk X ≤ 1) :
    X.ncard ≤ k := by
  rcases h.ncard_lt hX (j := 1) (by exact_mod_cast hr) (by norm_num) with h1 | h1 <;> omega

/-- A set of rank at most `2` has at most `2k` elements. -/
theorem ncard_le_ln (h : Strict4 M k) {X : Set α} (hX : X ⊆ M.E) (hr : M.eRk X ≤ 2) :
    X.ncard ≤ 2 * k := by
  rcases h.ncard_lt hX (j := 2) (by exact_mod_cast hr) (by norm_num) with h1 | h1 <;> omega

/-- A set of rank at most `3` has at most `3k+1` elements. -/
theorem ncard_le_pl (h : Strict4 M k) {X : Set α} (hX : X ⊆ M.E) (hr : M.eRk X ≤ 3) :
    X.ncard ≤ 3 * k + 1 := by
  rcases h.ncard_lt hX (j := 3) (by exact_mod_cast hr) (by norm_num) with h1 | h1 <;> omega

/-- A set of rank at most `1` lies in the closure of each of its elements. -/
theorem subset_closure_singleton (h : Strict4 M k) {Y : Set α} (hY : Y ⊆ M.E)
    (hYr : M.eRk Y ≤ 1) {e : α} (he : e ∈ Y) : Y ⊆ M.closure {e} :=
  subset_closure_of_eRk_le h.finite (singleton_subset_iff.2 he) hY
    (hYr.trans (h.one_le_eRk (singleton_subset_iff.2 (hY he)) (singleton_nonempty e)))

/-- An independent set meets a set of rank at most `j` in at most `j` elements. -/
theorem indep_inter_ncard_le (h : Strict4 M k) {D Y : Set α} (hD : M.Indep D) {j : ℕ}
    (hY : M.eRk Y ≤ j) : (D ∩ Y).ncard ≤ j := by
  have hfin : (D ∩ Y).Finite := h.finite.subset (inter_subset_left.trans hD.subset_ground)
  have h1 : M.eRk (D ∩ Y) = (D ∩ Y).encard := (hD.subset inter_subset_left).eRk_eq_encard
  have h2 : M.eRk (D ∩ Y) ≤ M.eRk Y := M.eRk_mono inter_subset_right
  rw [h1, ← hfin.cast_ncard_eq] at h2
  exact_mod_cast h2.trans hY

/-- A set not inside the flat `F` meets it in a set of smaller rank. -/
theorem exists_eRk_inter_flat_lt (h : Strict4 M k) {X F : Set α} (hX : X ⊆ M.E)
    (hF : M.IsFlat F) (hXF : ¬ X ⊆ F) {j : ℕ} (hj : M.eRk X = j) :
    ∃ i : ℕ, M.eRk (X ∩ F) = i ∧ i < j := by
  obtain ⟨i, hi, -⟩ := h.exists_eRk_eq (X ∩ F)
  have hlt : M.eRk (X ∩ F) < M.eRk X := by
    by_contra hle
    push_neg at hle
    exact hXF ((subset_closure_of_eRk_le h.finite inter_subset_left hX hle).trans
      ((M.closure_subset_closure inter_subset_right).trans_eq hF.closure))
  rw [hi, hj] at hlt
  exact ⟨i, hi, by exact_mod_cast hlt⟩

/-- Two distinct flats of the same rank meet in a set of smaller rank. -/
theorem exists_eRk_inter_lt_of_ne (h : Strict4 M k) {F G : Set α} (hF : M.IsFlat F)
    (hG : M.IsFlat G) {j : ℕ} (hFr : M.eRk F = j) (hGr : M.eRk G = j) (hne : F ≠ G) :
    ∃ i : ℕ, M.eRk (F ∩ G) = i ∧ i < j := by
  have hFG : ¬ F ⊆ G := fun hsub => hne (Subset.antisymm hsub
    ((subset_closure_of_eRk_le h.finite hsub hG.subset_ground
      (le_of_eq (by rw [hFr, hGr]))).trans_eq hF.closure))
  exact h.exists_eRk_inter_flat_lt hF.subset_ground hG hFG hFr

/-- An independent set with `4` elements is a basis. -/
theorem isBase_of_indep_ncard (h : Strict4 M k) {S : Set α} (hS : M.Indep S)
    (hn : S.ncard = 4) : M.IsBase S := by
  have hfin : S.Finite := h.finite.subset hS.subset_ground
  have h4 : S.encard = (4 : ℕ∞) := by
    have := hfin.cast_ncard_eq
    rw [hn] at this
    exact_mod_cast this.symm
  exact hS.isBase_of_eRk_ge hfin (le_of_eq (by rw [h.rank, hS.eRk_eq_encard, h4]))

end Strict4

namespace HitDanger

/-! ### Counting over a partition -/

/-- For a family partitioning `R`, the traces on `Y ⊆ R` add up to `|Y|`. -/
theorem sum_inter_eq [NeZero k] {D : ZMod k → Set α} {R Y : Set α} (hRfin : R.Finite)
    (hYR : Y ⊆ R) (hD : ∀ e ∈ R, ∃! x, e ∈ D x) : ∑ x, (D x ∩ Y).ncard = Y.ncard := by
  classical
  have hYfin : Y.Finite := hRfin.subset hYR
  have h1 : ∀ x, (D x ∩ Y).ncard = ∑ y ∈ hYfin.toFinset, if y ∈ D x then 1 else 0 := by
    intro x
    rw [← Finset.card_filter, ← Set.ncard_coe_finset]
    congr 1
    ext y
    simp [and_comm]
  have h2 : ∀ y ∈ hYfin.toFinset, ∑ x, (if y ∈ D x then 1 else 0) = 1 := by
    intro y hy
    obtain ⟨x, hx, huniq⟩ := hD y (hYR (hYfin.mem_toFinset.mp hy))
    have heq : (Finset.univ.filter fun l => y ∈ D l) = {x} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨huniq l, by rintro rfl; exact hx⟩
    calc ∑ l, (if y ∈ D l then 1 else 0) = (Finset.univ.filter fun l => y ∈ D l).card :=
          (Finset.card_filter _ _).symm
      _ = 1 := by rw [heq, Finset.card_singleton]
  rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_comm, Finset.sum_congr rfl h2,
    Finset.sum_const, smul_eq_mul, mul_one, ← Set.ncard_eq_toFinset_card Y hYfin]

/-- With every trace at most `r`: `|Y| ≤ |D x ∩ Y| + (k-1) r`. -/
theorem ncard_le_one_term [NeZero k] {D : ZMod k → Set α} {Y : Set α}
    (hsum : ∑ x, (D x ∩ Y).ncard = Y.ncard) {r : ℕ} (hr : ∀ x, (D x ∩ Y).ncard ≤ r)
    (x : ZMod k) : Y.ncard ≤ (D x ∩ Y).ncard + (k - 1) * r := by
  rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  have hle : ∑ l ∈ Finset.univ.erase x, (D l ∩ Y).ncard ≤ ∑ l ∈ Finset.univ.erase x, r :=
    Finset.sum_le_sum fun l _ => hr l
  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ x),
    Finset.card_univ, ZMod.card] at hle
  generalize (k - 1) * r = c at hle ⊢
  omega

/-- With every trace at most `r`: `|Y| ≤ |D x ∩ Y| + |D y ∩ Y| + (k-2) r` for `x ≠ y`. -/
theorem ncard_le_two_terms [NeZero k] {D : ZMod k → Set α} {Y : Set α}
    (hsum : ∑ x, (D x ∩ Y).ncard = Y.ncard) {r : ℕ} (hr : ∀ x, (D x ∩ Y).ncard ≤ r)
    {x y : ZMod k} (hxy : x ≠ y) :
    Y.ncard ≤ (D x ∩ Y).ncard + (D y ∩ Y).ncard + (k - 2) * r := by
  have hy : y ∈ Finset.univ.erase x := Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩
  rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ x), ← Finset.add_sum_erase _ _ hy]
  have hle : ∑ l ∈ (Finset.univ.erase x).erase y, (D l ∩ Y).ncard ≤
      ∑ l ∈ (Finset.univ.erase x).erase y, r := Finset.sum_le_sum fun l _ => hr l
  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hy,
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, ZMod.card] at hle
  have hc : k - 1 - 1 = k - 2 := by omega
  rw [hc] at hle
  generalize (k - 2) * r = c at hle ⊢
  omega

/-! ### The element `e₀` -/

/-- Some element of a plane with `3k+1` elements lies on no `k`-point. -/
theorem exists_light_elem (h : Strict4 M k) (hk : 2 ≤ k) {P : Set α} (hPf : M.IsFlat P)
    (hPn : P.ncard = 3 * k + 1) : ∃ e0 ∈ P, (M.closure {e0}).ncard + 1 ≤ k := by
  by_contra hno
  push_neg at hno
  have hPE := hPf.subset_ground
  have hPfin : P.Finite := h.finite.subset hPE
  -- every element of `P` lies on a `k`-point inside `P`
  have hcl : ∀ e ∈ P, M.closure {e} ⊆ P ∧ (M.closure {e}).ncard = k := by
    intro e he
    have hsub : M.closure {e} ⊆ P :=
      (M.closure_subset_closure (singleton_subset_iff.2 he)).trans_eq hPf.closure
    have hle := h.ncard_le_pt (M.closure_subset_ground _)
      (by rw [M.eRk_closure_eq]; exact M.eRk_singleton_le e)
    have hge := hno e he
    exact ⟨hsub, by omega⟩
  have hdisj : ∀ e ∈ P, ∀ f ∈ P, f ∉ M.closure {e} →
      Disjoint (M.closure {e}) (M.closure {f}) := by
    intro e he f hf hfe
    rw [Set.disjoint_left]
    intro x hxe hxf
    apply hfe
    have h1 : M.closure {f} ⊆ M.closure {x} :=
      h.subset_closure_singleton (M.closure_subset_ground _)
        (by rw [M.eRk_closure_eq]; exact M.eRk_singleton_le f) hxf
    have h2 : M.closure {x} ⊆ M.closure {e} :=
      (M.closure_subset_closure (singleton_subset_iff.2 hxe)).trans_eq
        (M.isFlat_closure _).closure
    exact h2 (h1 (M.subset_closure _ (singleton_subset_iff.2 (hPE hf)) (mem_singleton f)))
  -- four disjoint `k`-points in `P`
  obtain ⟨e1, he1⟩ : P.Nonempty := (Set.ncard_pos hPfin).1 (by omega)
  obtain ⟨hs1, hn1⟩ := hcl e1 he1
  have hf1 : (M.closure {e1}).Finite := hPfin.subset hs1
  obtain ⟨e2, he2, he2'⟩ : ∃ e2 ∈ P, e2 ∉ M.closure {e1} := by
    by_contra hc
    push_neg at hc
    have := Set.ncard_le_ncard (fun x hx => hc x hx : P ⊆ M.closure {e1}) hf1
    omega
  obtain ⟨hs2, hn2⟩ := hcl e2 he2
  have hf2 : (M.closure {e2}).Finite := hPfin.subset hs2
  have d12 := hdisj e1 he1 e2 he2 he2'
  obtain ⟨e3, he3, he3'⟩ : ∃ e3 ∈ P, e3 ∉ M.closure {e1} ∪ M.closure {e2} := by
    by_contra hc
    push_neg at hc
    have h1 := Set.ncard_le_ncard (fun x hx => hc x hx : P ⊆ M.closure {e1} ∪ M.closure {e2})
      (hf1.union hf2)
    have h2 := Set.ncard_union_le (M.closure {e1}) (M.closure {e2})
    omega
  obtain ⟨hs3, hn3⟩ := hcl e3 he3
  have hf3 : (M.closure {e3}).Finite := hPfin.subset hs3
  have d13 := hdisj e1 he1 e3 he3 fun h' => he3' (Or.inl h')
  have d23 := hdisj e2 he2 e3 he3 fun h' => he3' (Or.inr h')
  obtain ⟨e4, he4, he4'⟩ :
      ∃ e4 ∈ P, e4 ∉ M.closure {e1} ∪ M.closure {e2} ∪ M.closure {e3} := by
    by_contra hc
    push_neg at hc
    have h1 := Set.ncard_le_ncard
      (fun x hx => hc x hx : P ⊆ M.closure {e1} ∪ M.closure {e2} ∪ M.closure {e3})
      ((hf1.union hf2).union hf3)
    have h2 := Set.ncard_union_le (M.closure {e1} ∪ M.closure {e2}) (M.closure {e3})
    have h3 := Set.ncard_union_le (M.closure {e1}) (M.closure {e2})
    omega
  obtain ⟨hs4, hn4⟩ := hcl e4 he4
  have hf4 : (M.closure {e4}).Finite := hPfin.subset hs4
  have d14 := hdisj e1 he1 e4 he4 fun h' => he4' (Or.inl (Or.inl h'))
  have d24 := hdisj e2 he2 e4 he4 fun h' => he4' (Or.inl (Or.inr h'))
  have d34 := hdisj e3 he3 e4 he4 fun h' => he4' (Or.inr h')
  have u12 := Set.ncard_union_eq d12 hf1 hf2
  have u123 := Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d13, d23⟩) (hf1.union hf2) hf3
  have u1234 := Set.ncard_union_eq
    (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨d14, d24⟩, d34⟩)
    ((hf1.union hf2).union hf3) hf4
  have hsub := Set.ncard_le_ncard (union_subset (union_subset (union_subset hs1 hs2) hs3) hs4)
    hPfin
  omega

/-! ### The element `c` -/

/-- A choice of `c ∉ P` such that every point of `C₀ = E - P - c` has at most `k-1` elements, and
any two distinct planes through `C₀` meet `P` inside one small set `Q₀`. -/
theorem exists_c (h : Strict4 M k) (hk : 3 ≤ k) {P : Set α} (hPf : M.IsFlat P)
    (hPn : P.ncard = 3 * k + 1) :
    ∃ c ∈ M.E, c ∉ P ∧ (∀ Y ⊆ (M.E \ P) \ {c}, M.eRk Y ≤ 1 → Y.ncard + 1 ≤ k) ∧
      ∃ Q0 : Set α, ∀ F G : Set α, M.IsFlat F → M.eRk F = 3 → (M.E \ P) \ {c} ⊆ F →
        M.IsFlat G → M.eRk G = 3 → (M.E \ P) \ {c} ⊆ G → F ≠ G →
          F ∩ G ∩ P ⊆ Q0 ∧ Q0.ncard + 1 ≤ k ∧ Q0.Finite := by
  have hPE := hPf.subset_ground
  have hCE : M.E \ P ⊆ M.E := Set.sdiff_subset
  have hCfin : (M.E \ P).Finite := h.finite.subset hCE
  have hCn : (M.E \ P).ncard = k + 1 := by
    have := Set.ncard_sdiff_add_ncard_of_subset hPE h.finite
    have := h.ncard_ground
    omega
  -- if `E - P ⊆ cl(C₀)`, the planes through `C₀` contain `E - P` and meet inside `cl(E - P)`
  have hplanes : ∀ c ∈ M.E \ P, M.E \ P ⊆ M.closure ((M.E \ P) \ {c}) →
      ∃ Q0 : Set α, ∀ F G : Set α, M.IsFlat F → M.eRk F = 3 → (M.E \ P) \ {c} ⊆ F →
        M.IsFlat G → M.eRk G = 3 → (M.E \ P) \ {c} ⊆ G → F ≠ G →
          F ∩ G ∩ P ⊆ Q0 ∧ Q0.ncard + 1 ≤ k ∧ Q0.Finite := by
    intro c hcC hcl
    refine ⟨M.closure (M.E \ P) ∩ P, fun F G hF hFr hCF hG hGr hCG hFG => ?_⟩
    have hCF' : M.E \ P ⊆ F := hcl.trans ((M.closure_subset_closure hCF).trans_eq hF.closure)
    have hCG' : M.E \ P ⊆ G := hcl.trans ((M.closure_subset_closure hCG).trans_eq hG.closure)
    obtain ⟨i, hi, hi3⟩ := h.exists_eRk_inter_lt_of_ne hF hG (j := 3) (by exact_mod_cast hFr)
      (by exact_mod_cast hGr) hFG
    obtain ⟨s, hs, -⟩ := h.exists_eRk_eq (M.E \ P)
    have hs2 : 2 ≤ s := by
      by_contra hs2
      have := h.ncard_le_pt hCE (by rw [hs]; exact_mod_cast (show s ≤ 1 by omega))
      omega
    have hsi : s ≤ i := by
      have := M.eRk_mono (subset_inter hCF' hCG')
      rw [hs, hi] at this
      exact_mod_cast this
    have hsub : F ∩ G ⊆ M.closure (M.E \ P) :=
      subset_closure_of_eRk_le h.finite (subset_inter hCF' hCG')
        (inter_subset_left.trans hF.subset_ground)
        (by rw [hi, hs]; exact_mod_cast (show i ≤ s by omega))
    have hclE := M.closure_subset_ground (M.E \ P)
    have hcl2 := h.ncard_le_ln hclE
      (by rw [M.eRk_closure_eq, hs]; exact_mod_cast (show s ≤ 2 by omega))
    have hdisj : Disjoint (M.closure (M.E \ P) ∩ P) (M.E \ P) :=
      Set.disjoint_left.2 fun _ hz hz' => hz'.2 hz.2
    have hU := Set.ncard_union_eq hdisj (h.finite.subset (inter_subset_left.trans hclE)) hCfin
    have hle := Set.ncard_le_ncard
      (union_subset (inter_subset_left : M.closure (M.E \ P) ∩ P ⊆ M.closure (M.E \ P))
        (M.subset_closure _ hCE)) (h.finite.subset hclE)
    refine ⟨fun z hz => ⟨hsub hz.1, hz.2⟩, by omega,
      h.finite.subset (inter_subset_left.trans hclE)⟩
  by_cases hQ : ∃ Q ⊆ M.E \ P, M.eRk Q ≤ 1 ∧ k ≤ Q.ncard
  · -- `c` in the `k`-point `Q` inside `E - P`
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
    have hC0E : (M.E \ P) \ {c} ⊆ M.E := Set.sdiff_subset.trans hCE
    have hc'C0 : c' ∈ (M.E \ P) \ {c} :=
      ⟨hQC hc'Q, fun h' => hc'c (Set.mem_singleton_iff.1 h')⟩
    have hccl : c ∈ M.closure ((M.E \ P) \ {c}) :=
      M.closure_subset_closure (singleton_subset_iff.2 hc'C0)
        (h.subset_closure_singleton (hQC.trans hCE) hQr hc'Q hcQ)
    have hcl : M.E \ P ⊆ M.closure ((M.E \ P) \ {c}) := by
      intro z hz
      by_cases hzc : z = c
      · rw [hzc]
        exact hccl
      · exact M.subset_closure _ hC0E ⟨hz, fun h' => hzc (Set.mem_singleton_iff.1 h')⟩
    refine ⟨c, hcC.1, hcC.2, ?_, hplanes c hcC hcl⟩
    intro Y hY hYr
    by_contra hbig
    have hYC : Y ⊆ M.E \ P := hY.trans Set.sdiff_subset
    have hYfin : Y.Finite := hCfin.subset hYC
    have hcY : c ∉ Y := fun hcY => (hY hcY).2 (mem_singleton c)
    by_cases hmeet : (Y ∩ Q).Nonempty
    · -- `Y` and `Q` lie on one point, which would contain `Y + c`
      obtain ⟨e, heY, heQ⟩ := hmeet
      have hYcl := h.subset_closure_singleton (hYC.trans hCE) hYr heY
      have hQcl := h.subset_closure_singleton (hQC.trans hCE) hQr heQ
      have hr : M.eRk (insert c Y) ≤ 1 := by
        refine (M.eRk_mono (insert_subset (hQcl hcQ) hYcl)).trans ?_
        rw [M.eRk_closure_eq]
        exact M.eRk_singleton_le e
      have h1 := h.ncard_le_pt (insert_subset (hCE hcC) (hYC.trans hCE)) hr
      have h2 := Set.ncard_insert_of_notMem hcY hYfin
      omega
    · have hdisj : Disjoint Y Q :=
        Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hmeet)
      have h1 := Set.ncard_union_eq hdisj hYfin hQfin
      have h2 := Set.ncard_le_ncard (union_subset hYC hQC) hCfin
      omega
  push_neg at hQ
  obtain ⟨I, hI⟩ := M.exists_isBasis (M.E \ P) hCE
  by_cases hIC : M.E \ P ⊆ I
  · -- `E - P` is independent: no two planes contain `C₀`
    obtain ⟨c, hcC⟩ : (M.E \ P).Nonempty := (Set.ncard_pos hCfin).1 (by omega)
    have hCind : M.Indep (M.E \ P) := hI.indep.subset hIC
    refine ⟨c, hcC.1, hcC.2, fun Y hY hYr => ?_, ∅, fun F G hF hFr hCF hG hGr hCG hFG => ?_⟩
    · -- an independent set of rank at most `1` has at most one element
      have hYind : M.Indep Y := hCind.subset (hY.trans Set.sdiff_subset)
      have hYfin : Y.Finite := hCfin.subset (hY.trans Set.sdiff_subset)
      have h1 : Y.encard ≤ 1 := by
        rw [← hYind.eRk_eq_encard]
        exact hYr
      rw [← hYfin.cast_ncard_eq] at h1
      have h2 : Y.ncard ≤ 1 := by exact_mod_cast h1
      omega
    · exfalso
      obtain ⟨i, hi, hi3⟩ := h.exists_eRk_inter_lt_of_ne hF hG (j := 3) (by exact_mod_cast hFr)
        (by exact_mod_cast hGr) hFG
      have hC0ind : M.Indep ((M.E \ P) \ {c}) := hCind.subset Set.sdiff_subset
      have hC0fin : ((M.E \ P) \ {c}).Finite := hCfin.subset Set.sdiff_subset
      have hC0n : ((M.E \ P) \ {c}).ncard = k := by
        have := Set.ncard_sdiff_singleton_add_one hcC hCfin
        omega
      have hr := M.eRk_mono (subset_inter hCF hCG)
      rw [hC0ind.eRk_eq_encard, ← hC0fin.cast_ncard_eq, hC0n, hi] at hr
      have : k ≤ i := by exact_mod_cast hr
      omega
  · -- `c` outside a basis of `E - P`
    obtain ⟨c, hcC, hcI⟩ := Set.not_subset.1 hIC
    have hIC0 : I ⊆ (M.E \ P) \ {c} := fun z hz =>
      ⟨hI.subset hz, fun h' => hcI (by rw [← Set.mem_singleton_iff.1 h']; exact hz)⟩
    have hcl : M.E \ P ⊆ M.closure ((M.E \ P) \ {c}) :=
      calc M.E \ P ⊆ M.closure (M.E \ P) := M.subset_closure _ hCE
        _ = M.closure I := hI.closure_eq_closure.symm
        _ ⊆ M.closure ((M.E \ P) \ {c}) := M.closure_subset_closure hIC0
    refine ⟨c, hcC.1, hcC.2, fun Y hY hYr => ?_, hplanes c hcC hcl⟩
    have h1 := h.ncard_le_pt ((hY.trans Set.sdiff_subset).trans hCE) hYr
    have h2 := hQ Y (hY.trans Set.sdiff_subset) hYr
    omega

/-! ### The good triple -/

/-- A plane `F ≠ P` is bad (`|F ∩ P - D x| ≥ 2k-1`) for at most one triple. -/
theorem not_two_bad (h : Strict4 M k) (hk : 2 ≤ k) [NeZero k] {P F : Set α} {e0 : α}
    {D : ZMod k → Set α} (hPf : M.IsFlat P) (hPr : M.eRk P = 3) (hF : M.IsFlat F)
    (hFr : M.eRk F = 3) (hFP : F ≠ P) (hDind : ∀ x, M.Indep (D x))
    (hDpart : ∀ e ∈ P \ {e0}, ∃! x, e ∈ D x) {x y : ZMod k} (hxy : x ≠ y)
    (hx : 2 * k - 1 ≤ ((F ∩ P) \ D x).ncard) (hy : 2 * k - 1 ≤ ((F ∩ P) \ D y).ncard) :
    False := by
  have hPE := hPf.subset_ground
  have hlE : F ∩ P ⊆ M.E := inter_subset_right.trans hPE
  have hlfin : (F ∩ P).Finite := h.finite.subset hlE
  obtain ⟨i, hi, hi3⟩ := h.exists_eRk_inter_lt_of_ne hF hPf (j := 3) (by exact_mod_cast hFr)
    (by exact_mod_cast hPr) hFP
  have hl2 : M.eRk (F ∩ P) ≤ ((2 : ℕ) : ℕ∞) := by
    rw [hi]
    exact_mod_cast (show i ≤ 2 by omega)
  have hln := h.ncard_le_ln hlE (by exact_mod_cast hl2)
  -- count the traces on `ℓ' = F ∩ P - e₀`
  have hl'R : (F ∩ P) \ {e0} ⊆ P \ {e0} := fun z hz => ⟨hz.1.2, hz.2⟩
  have hsum := sum_inter_eq (h.finite.subset (Set.sdiff_subset.trans hPE)) hl'R hDpart
  have hr : ∀ z, (D z ∩ ((F ∩ P) \ {e0})).ncard ≤ 2 := fun z =>
    h.indep_inter_ncard_le (hDind z) ((M.eRk_mono Set.sdiff_subset).trans hl2)
  have htwo := ncard_le_two_terms hsum hr hxy
  have hsx : (D x ∩ ((F ∩ P) \ {e0})).ncard ≤ ((F ∩ P) ∩ D x).ncard :=
    Set.ncard_le_ncard (fun z hz => ⟨hz.2.1, hz.1⟩) (hlfin.subset inter_subset_left)
  have hsy : (D y ∩ ((F ∩ P) \ {e0})).ncard ≤ ((F ∩ P) ∩ D y).ncard :=
    Set.ncard_le_ncard (fun z hz => ⟨hz.2.1, hz.1⟩) (hlfin.subset inter_subset_left)
  have hx' := Set.ncard_inter_add_ncard_sdiff_eq_ncard (F ∩ P) (D x) hlfin
  have hy' := Set.ncard_inter_add_ncard_sdiff_eq_ncard (F ∩ P) (D y) hlfin
  have hl' : (F ∩ P).ncard ≤ ((F ∩ P) \ {e0}).ncard + 1 := by
    have h1 : F ∩ P ⊆ insert e0 ((F ∩ P) \ {e0}) := fun z hz => by
      by_cases hz0 : z = e0
      · exact Or.inl hz0
      · exact Or.inr ⟨hz, hz0⟩
    exact (Set.ncard_le_ncard h1 ((hlfin.subset Set.sdiff_subset).insert e0)).trans
      (Set.ncard_insert_le _ _)
  omega

/-- Three distinct planes through `C₀` cannot each meet `P` in `2k-1` elements: their traces on
`P` overlap only inside `Q₀`, so they would need `(2k-1) + k + k > 3k+1` elements of `P`. -/
theorem not_three_planes (h : Strict4 M k) (hk : 3 ≤ k) {P C0 Q0 : Set α} (hPf : M.IsFlat P)
    (hPn : P.ncard = 3 * k + 1)
    (hpairs : ∀ F G : Set α, M.IsFlat F → M.eRk F = 3 → C0 ⊆ F → M.IsFlat G → M.eRk G = 3 →
      C0 ⊆ G → F ≠ G → F ∩ G ∩ P ⊆ Q0 ∧ Q0.ncard + 1 ≤ k ∧ Q0.Finite)
    {F1 F2 F3 : Set α} (h1 : M.IsFlat F1) (h1r : M.eRk F1 = 3) (h1C : C0 ⊆ F1)
    (h2 : M.IsFlat F2) (h2r : M.eRk F2 = 3) (h2C : C0 ⊆ F2)
    (h3 : M.IsFlat F3) (h3r : M.eRk F3 = 3) (h3C : C0 ⊆ F3)
    (h12 : F1 ≠ F2) (h13 : F1 ≠ F3) (h23 : F2 ≠ F3)
    (n1 : 2 * k - 1 ≤ (F1 ∩ P).ncard) (n2 : 2 * k - 1 ≤ (F2 ∩ P).ncard)
    (n3 : 2 * k - 1 ≤ (F3 ∩ P).ncard) : False := by
  have hPfin : P.Finite := h.finite.subset hPf.subset_ground
  obtain ⟨s12, hQ, hQfin⟩ := hpairs F1 F2 h1 h1r h1C h2 h2r h2C h12
  have s13 := (hpairs F1 F3 h1 h1r h1C h3 h3r h3C h13).1
  have s23 := (hpairs F2 F3 h2 h2r h2C h3 h3r h3C h23).1
  have d12 : Disjoint (F1 ∩ P) ((F2 ∩ P) \ Q0) :=
    Set.disjoint_left.2 fun _ hz1 hz2 => hz2.2 (s12 ⟨⟨hz1.1, hz2.1.1⟩, hz1.2⟩)
  have d13 : Disjoint (F1 ∩ P) ((F3 ∩ P) \ Q0) :=
    Set.disjoint_left.2 fun _ hz1 hz3 => hz3.2 (s13 ⟨⟨hz1.1, hz3.1.1⟩, hz1.2⟩)
  have d23 : Disjoint ((F2 ∩ P) \ Q0) ((F3 ∩ P) \ Q0) :=
    Set.disjoint_left.2 fun _ hz2 hz3 => hz3.2 (s23 ⟨⟨hz2.1.1, hz3.1.1⟩, hz2.1.2⟩)
  have f1 : (F1 ∩ P).Finite := hPfin.subset inter_subset_right
  have f2 : ((F2 ∩ P) \ Q0).Finite := hPfin.subset (Set.sdiff_subset.trans inter_subset_right)
  have f3 : ((F3 ∩ P) \ Q0).Finite := hPfin.subset (Set.sdiff_subset.trans inter_subset_right)
  have u12 := Set.ncard_union_eq d12 f1 f2
  have u123 := Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d13, d23⟩) (f1.union f2) f3
  have hsub : (F1 ∩ P) ∪ ((F2 ∩ P) \ Q0) ∪ ((F3 ∩ P) \ Q0) ⊆ P :=
    union_subset (union_subset inter_subset_right (Set.sdiff_subset.trans inter_subset_right))
      (Set.sdiff_subset.trans inter_subset_right)
  have hsubn := Set.ncard_le_ncard hsub hPfin
  have c2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard (F2 ∩ P) Q0 (hPfin.subset inter_subset_right)
  have c3 := Set.ncard_inter_add_ncard_sdiff_eq_ncard (F3 ∩ P) Q0 (hPfin.subset inter_subset_right)
  have q2 := Set.ncard_le_ncard (inter_subset_right : (F2 ∩ P) ∩ Q0 ⊆ Q0) hQfin
  have q3 := Set.ncard_le_ncard (inter_subset_right : (F3 ∩ P) ∩ Q0 ⊆ Q0) hQfin
  omega

/-- Some triple has no bad plane through `C₀`. -/
theorem exists_good_triple (h : Strict4 M k) (hk : 3 ≤ k) [NeZero k] {P C0 Q0 : Set α}
    {e0 : α} (hPf : M.IsFlat P) (hPr : M.eRk P = 3) (hPn : P.ncard = 3 * k + 1)
    {D : ZMod k → Set α} (hDind : ∀ x, M.Indep (D x))
    (hDpart : ∀ e ∈ P \ {e0}, ∃! x, e ∈ D x)
    (hpairs : ∀ F G : Set α, M.IsFlat F → M.eRk F = 3 → C0 ⊆ F → M.IsFlat G → M.eRk G = 3 →
      C0 ⊆ G → F ≠ G → F ∩ G ∩ P ⊆ Q0 ∧ Q0.ncard + 1 ≤ k ∧ Q0.Finite) :
    ∃ x, ∀ F, M.IsFlat F → M.eRk F = 3 → F ≠ P → C0 ⊆ F →
      ((F ∩ P) \ D x).ncard + 2 ≤ 2 * k := by
  have hPfin : P.Finite := h.finite.subset hPf.subset_ground
  by_contra hno
  push_neg at hno
  obtain ⟨a, -, b, -, c, -, hab, hac, hbc⟩ := Finset.two_lt_card.1
    (show 2 < (Finset.univ : Finset (ZMod k)).card by rw [Finset.card_univ, ZMod.card]; omega)
  obtain ⟨Fa, haf, har, haP, haC, han⟩ := hno a
  obtain ⟨Fb, hbf, hbr, hbP, hbC, hbn⟩ := hno b
  obtain ⟨Fc, hcf, hcr, hcP, hcC, hcn⟩ := hno c
  have hbad : ∀ {F : Set α} {x y : ZMod k}, M.IsFlat F → M.eRk F = 3 → F ≠ P → x ≠ y →
      2 * k < ((F ∩ P) \ D x).ncard + 2 → 2 * k < ((F ∩ P) \ D y).ncard + 2 → False :=
    fun hF hFr hFP hxy hx hy =>
      not_two_bad h (by omega) hPf hPr hF hFr hFP hDind hDpart hxy (by omega) (by omega)
  have hab' : Fa ≠ Fb := fun hEq => hbad hbf hbr hbP hab (by rw [← hEq]; exact han) hbn
  have hac' : Fa ≠ Fc := fun hEq => hbad hcf hcr hcP hac (by rw [← hEq]; exact han) hcn
  have hbc' : Fb ≠ Fc := fun hEq => hbad hcf hcr hcP hbc (by rw [← hEq]; exact hbn) hcn
  have ma := Set.ncard_le_ncard (Set.sdiff_subset : (Fa ∩ P) \ D a ⊆ Fa ∩ P)
    (hPfin.subset inter_subset_right)
  have mb := Set.ncard_le_ncard (Set.sdiff_subset : (Fb ∩ P) \ D b ⊆ Fb ∩ P)
    (hPfin.subset inter_subset_right)
  have mc := Set.ncard_le_ncard (Set.sdiff_subset : (Fc ∩ P) \ D c ⊆ Fc ∩ P)
    (hPfin.subset inter_subset_right)
  exact not_three_planes h hk hPf hPn hpairs haf har haC hbf hbr hbC hcf hcr hcC hab' hac' hbc'
    (by omega) (by omega) (by omega)

/-! ### Deletability -/

/-- **The choice lemma for a dangerous plane.** Let `D ⊆ P` be an independent triple and
`c ∉ P`, with `C₀ = E - P - c`. If every point and line inside `P - D` has at most `k-1` and
`2k-1` elements, every point inside `C₀` at most `k-1`, and every plane `F ≠ P` through `C₀` has
at most `2k-2` elements in `P - D`, then `D + c` is deletable. -/
theorem deletable_of_danger (h : Strict4 M k) (hk : 3 ≤ k) {P D : Set α} {c : α}
    (hPf : M.IsFlat P) (hPn : P.ncard = 3 * k + 1) (hD : M.Indep D) (hDP : D ⊆ P)
    (hDn : D.ncard = 3) (hcE : c ∈ M.E) (hcP : c ∉ P)
    (hpt : ∀ Y ⊆ P \ D, M.eRk Y ≤ 1 → Y.ncard + 1 ≤ k)
    (hln : ∀ Y ⊆ P \ D, M.eRk Y ≤ 2 → Y.ncard + 1 ≤ 2 * k)
    (hCpt : ∀ Y ⊆ (M.E \ P) \ {c}, M.eRk Y ≤ 1 → Y.ncard + 1 ≤ k)
    (hpl : ∀ F, M.IsFlat F → M.eRk F = 3 → F ≠ P → (M.E \ P) \ {c} ⊆ F →
      ((F ∩ P) \ D).ncard + 2 ≤ 2 * k) :
    Deletable M k (insert c D) := by
  have hPE := hPf.subset_ground
  have hfin : ∀ {Y : Set α}, Y ⊆ M.E → Y.Finite := fun hY => h.finite.subset hY
  -- `D + c` is a basis
  have hclD : M.closure D ⊆ P := (M.closure_subset_closure hDP).trans_eq hPf.closure
  have hcD : c ∉ D := fun hc => hcP (hDP hc)
  have hSind : M.Indep (insert c D) :=
    (hD.insert_indep_iff_of_notMem hcD).2 ⟨hcE, fun hc => hcP (hclD hc)⟩
  have hSn : (insert c D).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem hcD (hfin (hDP.trans hPE)), hDn]
  have hSbase := h.isBase_of_indep_ncard hSind hSn
  -- `E - P` has `k+1` elements and `C₀` has `k`
  have hCn : (M.E \ P).ncard = k + 1 := by
    have := Set.ncard_sdiff_add_ncard_of_subset hPE h.finite
    have := h.ncard_ground
    omega
  have hcC : c ∈ M.E \ P := ⟨hcE, hcP⟩
  have hC0n : ((M.E \ P) \ {c}).ncard = k := by
    have := Set.ncard_sdiff_singleton_add_one hcC (hfin Set.sdiff_subset)
    omega
  have hC0fin : ((M.E \ P) \ {c}).Finite := hfin (Set.sdiff_subset.trans Set.sdiff_subset)
  have hPD : (P \ D).ncard + 3 = 3 * k + 1 := by
    have := Set.ncard_sdiff_add_ncard_of_subset hDP (hfin hPE)
    omega
  refine ⟨hSbase, fun X hX => ?_⟩
  have hXS : X ⊆ M.E \ insert c D := hX
  have hXE : X ⊆ M.E := hXS.trans Set.sdiff_subset
  have hXfin : X.Finite := hfin hXE
  rw [Matroid.restrict_eRk_eq M hXS]
  obtain ⟨j, hj, hj4⟩ := h.exists_eRk_eq X
  rw [← hXfin.cast_ncard_eq, hj]
  suffices hN : 4 * X.ncard ≤ (4 * k - 2) * j by exact_mod_cast hN
  -- the part of `X` in `P` avoids `D`, the rest lies in `C₀`
  have hXP : X ∩ P ⊆ P \ D :=
    fun z hz => ⟨hz.2, fun hzD => (hXS hz.1).2 (mem_insert_of_mem c hzD)⟩
  have hXC : X \ P ⊆ (M.E \ P) \ {c} := by
    intro z hz
    refine ⟨⟨hXE hz.1, hz.2⟩, fun hzc => (hXS hz.1).2 ?_⟩
    rw [Set.mem_singleton_iff.1 hzc]
    exact mem_insert c D
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard X P hXfin
  have hw : (X \ P).ncard ≤ k := (Set.ncard_le_ncard hXC hC0fin).trans hC0n.le
  have hXPn : (X ∩ P).ncard ≤ (P \ D).ncard :=
    Set.ncard_le_ncard hXP (hfin (Set.sdiff_subset.trans hPE))
  have hX0 : X.ncard = 0 ∨ 1 ≤ j := by
    rcases X.eq_empty_or_nonempty with he | hne
    · left
      rw [he, Set.ncard_empty]
    · right
      have := h.one_le_eRk hXE hne
      rw [hj] at this
      exact_mod_cast this
  by_cases hXsubP : X ⊆ P
  · have hw0 : (X \ P).ncard = 0 := by rw [Set.sdiff_eq_empty.2 hXsubP, Set.ncard_empty]
    have hXP' : X ⊆ P \ D := fun z hz => hXP ⟨hz, hXsubP hz⟩
    interval_cases j
    · omega
    · have := hpt X hXP' (by exact_mod_cast hj.le)
      omega
    · have := hln X hXP' (by exact_mod_cast hj.le)
      omega
    · omega
    · omega
  obtain ⟨i, hi, hij⟩ := h.exists_eRk_inter_flat_lt hXE hPf hXsubP hj
  by_cases hfull : (X \ P).ncard = k
  · -- `X ⊇ C₀`
    have hXCeq : X \ P = (M.E \ P) \ {c} := Set.eq_of_subset_of_ncard_le hXC (by omega) hC0fin
    have hC0X : (M.E \ P) \ {c} ⊆ X := by
      rw [← hXCeq]
      exact Set.sdiff_subset
    interval_cases j
    · omega
    · have h1 : M.eRk (X \ P) ≤ 1 := by
        have := (M.eRk_mono (Set.sdiff_subset : X \ P ⊆ X)).trans hj.le
        exact_mod_cast this
      have := hCpt (X \ P) hXC h1
      omega
    · have h1 : M.eRk (X ∩ P) ≤ 1 := by
        rw [hi]
        exact_mod_cast (show i ≤ 1 by omega)
      have := hpt (X ∩ P) hXP h1
      omega
    · -- `cl(X)` is a plane `≠ P` through `C₀`
      have hFr : M.eRk (M.closure X) = 3 := by
        rw [M.eRk_closure_eq]
        exact_mod_cast hj
      have hFP : M.closure X ≠ P := by
        intro hEq
        apply hXsubP
        rw [← hEq]
        exact M.subset_closure X hXE
      have hst := hpl (M.closure X) (M.isFlat_closure X) hFr hFP
        (hC0X.trans (M.subset_closure X hXE))
      have hsub : X ∩ P ⊆ (M.closure X ∩ P) \ D :=
        fun z hz => ⟨⟨M.subset_closure X hXE hz.1, hz.2⟩, (hXP hz).2⟩
      have := Set.ncard_le_ncard hsub
        (hfin ((Set.sdiff_subset.trans inter_subset_right).trans hPE))
      omega
    · omega
  · interval_cases j
    · omega
    · -- `X ∩ P` is empty
      have hXP0 : (X ∩ P).ncard = 0 := by
        rcases (X ∩ P).eq_empty_or_nonempty with he | hne
        · rw [he, Set.ncard_empty]
        · exfalso
          have := h.one_le_eRk (inter_subset_left.trans hXE) hne
          rw [hi] at this
          have : 1 ≤ i := by exact_mod_cast this
          omega
      omega
    · have h1 : M.eRk (X ∩ P) ≤ 1 := by
        rw [hi]
        exact_mod_cast (show i ≤ 1 by omega)
      have := hpt (X ∩ P) hXP h1
      omega
    · have h1 : M.eRk (X ∩ P) ≤ 2 := by
        rw [hi]
        exact_mod_cast (show i ≤ 2 by omega)
      have := hln (X ∩ P) hXP h1
      omega
    · omega

end HitDanger

open HitDanger in
/-- **The hitting lemma with a dangerous plane**: a strict rank-4 matroid on `4k+2` elements,
`k ≥ 3`, with a plane of `3k+1` elements has a deletable basis. -/
theorem hitDanger (h : Strict4 M k) (hk : 3 ≤ k) {P : Set α} (hPf : M.IsFlat P)
    (hPr : M.eRk P = 3) (hPc : P.encard = ((3 * k + 1 : ℕ) : ℕ∞)) : ∃ S, Deletable M k S := by
  haveI : NeZero k := ⟨by omega⟩
  have hPE := hPf.subset_ground
  have hPfin : P.Finite := h.finite.subset hPE
  have hPn : P.ncard = 3 * k + 1 := by
    rw [← hPfin.cast_ncard_eq] at hPc
    exact_mod_cast hPc
  obtain ⟨e0, he0P, he0⟩ := exists_light_elem h (by omega) hPf hPn
  -- Edmonds: `P - e₀` splits into `k` independent triples
  have hRP : P \ {e0} ⊆ P := Set.sdiff_subset
  have hRfin : (P \ {e0}).Finite := hPfin.subset hRP
  have hRn : (P \ {e0}).ncard = 3 * k := by
    have := Set.ncard_sdiff_singleton_add_one he0P hPfin
    omega
  have hRr : M.eRk (P \ {e0}) = 3 := by
    obtain ⟨j, hj, -⟩ := h.exists_eRk_eq (P \ {e0})
    have hle : j ≤ 3 := by
      have := M.eRk_mono hRP
      rw [hj, hPr] at this
      exact_mod_cast this
    have hge : 3 ≤ j := by
      by_contra hlt
      have := h.ncard_le_ln (hRP.trans hPE) (by rw [hj]; exact_mod_cast (show j ≤ 2 by omega))
      omega
    rw [hj]
    exact_mod_cast (show j = 3 by omega)
  have hDense : UniformlyDenseRatio (M ↾ (P \ {e0})) k 1 := by
    intro X hX
    have hXR : X ⊆ P \ {e0} := hX
    have hXE : X ⊆ M.E := hXR.trans (hRP.trans hPE)
    have hXfin : X.Finite := hRfin.subset hXR
    rw [Matroid.restrict_eRk_eq M hXR]
    obtain ⟨j, hj, hj4⟩ := h.exists_eRk_eq X
    rw [← hXfin.cast_ncard_eq, hj]
    have hXn : X.ncard ≤ (P \ {e0}).ncard := Set.ncard_le_ncard hXR hRfin
    have hb : X.ncard ≤ k * j := by
      interval_cases j
      · rcases X.eq_empty_or_nonempty with he | hne
        · rw [he, Set.ncard_empty]
          omega
        · have := h.one_le_eRk hXE hne
          rw [hj] at this
          have : (1 : ℕ) ≤ 0 := by exact_mod_cast this
          omega
      · have := h.ncard_le_pt hXE (by exact_mod_cast hj.le)
        omega
      · have := h.ncard_le_ln hXE (by exact_mod_cast hj.le)
        omega
      · omega
      · omega
    have h1 : 1 * X.ncard ≤ k * j := by omega
    exact_mod_cast h1
  have hRankR : (M ↾ (P \ {e0})).eRank = ((3 : ℕ) : ℕ∞) := by
    rw [← Matroid.eRk_ground, Matroid.restrict_ground_eq, Matroid.restrict_eRk_eq _ subset_rfl]
    exact hRr.trans (by norm_num)
  have hRcard : (P \ {e0}).encard = ((3 * k : ℕ) : ℕ∞) := by
    rw [← hRfin.cast_ncard_eq, hRn]
  obtain ⟨D, hDbase, hDpart⟩ := VHT.edmonds_partition VHT.theorem_2_1 (M ↾ (P \ {e0}))
    (k := k) (n := 3 * k) (r := 3) (by omega) hRfin hRcard hRankR (Nat.mul_comm 3 k) hDense
  have hDR : ∀ x, D x ⊆ P \ {e0} := fun x => (hDbase x).subset_ground
  have hDind : ∀ x, M.Indep (D x) := fun x => (Matroid.restrict_indep_iff.1 (hDbase x).indep).1
  have hDn : ∀ x, (D x).ncard = 3 := by
    intro x
    have hc : (D x).encard = ((3 : ℕ) : ℕ∞) := (hDbase x).encard_eq_eRank.trans hRankR
    rw [← (hRfin.subset (hDR x)).cast_ncard_eq] at hc
    exact_mod_cast hc
  have hDpart' : ∀ e ∈ P \ {e0}, ∃! x, e ∈ D x := fun e he => hDpart e he
  -- every triple meets every `k`-point and every `2k`-line of `P`
  have hpt : ∀ x, ∀ Y ⊆ P \ D x, M.eRk Y ≤ 1 → Y.ncard + 1 ≤ k := by
    intro x Y hY hYr
    have hYE : Y ⊆ M.E := hY.trans (Set.sdiff_subset.trans hPE)
    have hle := h.ncard_le_pt hYE hYr
    by_contra hk'
    have he0Y : e0 ∉ Y := by
      intro he0Y
      have hsub := h.subset_closure_singleton hYE hYr he0Y
      have := Set.ncard_le_ncard hsub (h.finite.subset (M.closure_subset_ground _))
      omega
    have hYR : Y ⊆ P \ {e0} := fun z hz =>
      ⟨(hY hz).1, fun hz0 => he0Y (by rw [← Set.mem_singleton_iff.1 hz0]; exact hz)⟩
    have hsum := sum_inter_eq hRfin hYR hDpart'
    have hr : ∀ z, (D z ∩ Y).ncard ≤ 1 := fun z =>
      h.indep_inter_ncard_le (hDind z) (by exact_mod_cast hYr)
    have h1 := ncard_le_one_term hsum hr x
    have h0 : D x ∩ Y = ∅ :=
      Set.disjoint_iff_inter_eq_empty.1 (Set.disjoint_left.2 fun _ hz1 hz2 => (hY hz2).2 hz1)
    rw [h0, Set.ncard_empty] at h1
    omega
  have hln : ∀ x, ∀ Y ⊆ P \ D x, M.eRk Y ≤ 2 → Y.ncard + 1 ≤ 2 * k := by
    intro x Y hY hYr
    have hYE : Y ⊆ M.E := hY.trans (Set.sdiff_subset.trans hPE)
    have hYfin : Y.Finite := h.finite.subset hYE
    have hle := h.ncard_le_ln hYE hYr
    by_contra hk'
    have hY' : Y \ {e0} ⊆ P \ {e0} := fun z hz => ⟨(hY hz.1).1, hz.2⟩
    have hsum := sum_inter_eq hRfin hY' hDpart'
    have hr : ∀ z, (D z ∩ (Y \ {e0})).ncard ≤ 2 := fun z =>
      h.indep_inter_ncard_le (hDind z)
        ((M.eRk_mono Set.sdiff_subset).trans (by exact_mod_cast hYr))
    have h1 := ncard_le_one_term hsum hr x
    have h0 : D x ∩ (Y \ {e0}) = ∅ :=
      Set.disjoint_iff_inter_eq_empty.1
        (Set.disjoint_left.2 fun _ hz1 hz2 => (hY hz2.1).2 hz1)
    rw [h0, Set.ncard_empty] at h1
    have h2 : Y.ncard ≤ (Y \ {e0}).ncard + 1 := by
      have h3 : Y ⊆ insert e0 (Y \ {e0}) := fun z hz => by
        by_cases hz0 : z = e0
        · exact Or.inl hz0
        · exact Or.inr ⟨hz, hz0⟩
      exact (Set.ncard_le_ncard h3 ((hYfin.subset Set.sdiff_subset).insert e0)).trans
        (Set.ncard_insert_le _ _)
    omega
  -- the element `c` and the good triple
  obtain ⟨c, hcE, hcP, hCpt, Q0, hpairs⟩ := exists_c h hk hPf hPn
  obtain ⟨x, hpl⟩ := exists_good_triple h hk hPf hPr hPn hDind hDpart' hpairs
  exact ⟨_, deletable_of_danger h hk hPf hPn (hDind x) (fun z hz => (hDR x hz).1) (hDn x) hcE
    hcP (hpt x) (hln x) hCpt hpl⟩

end Hitting
end HigherRankKUM

#print axioms HigherRankKUM.Hitting.hitDanger
