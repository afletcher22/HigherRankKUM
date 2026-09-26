import Probe.Kum10Data
import Probe.ExtBridge
import Probe.Rank4.Hitting

/-!
# From matroids to `RankModelF`: the 10-element claims

Number the ground set of a rank-4 matroid `M`. The ranks of the sets named by bitmasks satisfy the
rank axioms. If `M` has no cyclic basis ordering, every cyclic order of the positions has a window
of rank below 4. With lower bounds by size and facts about named sets, this gives a `RankModelF`
(`rankModelF_of_pos`).

For the base lemmas the numbering puts a given flat first (`blockEquiv`), so that its bitmask
names it. The results are:

* `cbo_of_basePlane`: a uniformly dense rank-4 matroid on 10 elements with a 6-element flat plane
  `K` and `r(E - K) = c` has a cyclic basis ordering, given the certificate for `c`;
* `cbo_of_baseLine`: the same with a 4-element flat line;
* `cbo_of_light`: the same in the strict t=0 class with no 6-plane and no 4-line.
-/

namespace Probe.Enc

open Set HigherRankKUM
open scoped Matroid

variable {α : Type*}

/-! ### Rank models from a numbering -/

/-- With no cyclic basis ordering, every cyclic order of the positions has a window of rank
below `4`. -/
theorem maskRank_noCBO {M : Matroid α} (hRank : M.eRank = 4) {N : ℕ} (hN : 0 < N)
    (pos : Fin N ≃ M.E) (hno : ¬ ∃ τ : Fin N ≃ M.E, CyclicBasisOrder M 4 hN τ)
    (s : List ℕ) (hlen : s.length = N) (hcov : ∀ x < N, x ∈ s) (hbound : ∀ x ∈ s, x < N) :
    ∃ i < N, maskRank M pos (window s i) < 4 := by
  by_contra hall
  push_neg at hall
  have hlt : ∀ k : Fin N, s.getD k 0 < N := by
    intro k
    apply hbound
    have hk : (k : ℕ) < s.length := by omega
    rw [List.getD_eq_getElem?_getD]
    simp [hk]
  let p : Fin N → Fin N := fun k => ⟨s.getD k 0, hlt k⟩
  have hsurj : Function.Surjective p := by
    intro y
    obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.1 (hcov y y.2)
    refine ⟨⟨k, by omega⟩, Fin.ext ?_⟩
    simp only [p, List.getD_eq_getElem?_getD]
    simp [hk, hky]
  have hbij : Function.Bijective p := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  let τ : Fin N ≃ M.E := (Equiv.ofBijective p hbij).trans pos
  refine hno ⟨τ, fun i => isBase_cyclicWindow_of_four_le hRank hN τ i ?_⟩
  have hsub : maskSet pos (window s i) ⊆ cyclicWindow 4 hN τ i := by
    rintro x ⟨j, hj, rfl⟩
    rw [testBit_window, hlen] at hj
    obtain ⟨t, ht, htj⟩ := hj
    rw [cyclicWindow, Set.mem_range]
    refine ⟨⟨t, ht⟩, ?_⟩
    have hpj : p (cyclicIndex N hN i t) = j := Fin.ext (by simpa [p, cyclicIndex] using htj)
    simp [τ, hpj]
  have h2 := M.eRk_mono hsub
  rw [← maskRank_cast hRank pos] at h2
  calc (4 : ℕ∞) ≤ ((maskRank M pos (window s i) : ℕ) : ℕ∞) := by exact_mod_cast hall i i.2
    _ ≤ M.eRk (cyclicWindow 4 hN τ i) := h2

/-- The ranks of the sets named by bitmasks form a `RankModelF`, given its lower bounds and
facts. -/
noncomputable def rankModelF_of_pos {M : Matroid α} (hRank : M.eRank = 4) {N : ℕ} (hN : 0 < N)
    (pos : Fin N ≃ M.E) {lowTab : List ℕ} {facts : List (ℕ × ℕ × Bool)}
    (hlow : ∀ X, X < 2 ^ N → lowTab.getD (pc N X) 0 ≤ maskRank M pos X)
    (hfactT : ∀ X v, (X, v, true) ∈ facts → v ≤ maskRank M pos X)
    (hfactF : ∀ X v, (X, v, false) ∈ facts → maskRank M pos X < v)
    (hno : ¬ ∃ τ : Fin N ≃ M.E, CyclicBasisOrder M 4 hN τ) : RankModelF N lowTab facts where
  r := maskRank M pos
  card X _ := by
    have h := M.eRk_le_encard (maskSet pos X)
    rw [← maskRank_cast hRank pos X, encard_maskSet] at h
    exact_mod_cast h
  low := hlow
  mono X a _ ha _ := by
    have h := M.eRk_mono (show maskSet pos X ⊆ maskSet pos (X ||| 1 <<< a) by
      rw [maskSet_insert pos X a ha]
      exact subset_insert _ _)
    rw [← maskRank_cast hRank pos X, ← maskRank_cast hRank pos (X ||| 1 <<< a)] at h
    exact_mod_cast h
  ins X a _ ha _ := by
    have h := M.eRk_insert_le_add_one (pos ⟨a, ha⟩ : α) (maskSet pos X)
    rw [← maskSet_insert pos X a ha, ← maskRank_cast hRank pos X,
      ← maskRank_cast hRank pos (X ||| 1 <<< a)] at h
    exact_mod_cast h
  sub X a b _ hab hbN ha hb := by
    have haN : a < N := by omega
    have hA := maskSet_insert pos X a haN
    have hB := maskSet_insert pos X b hbN
    have hAB := maskSet_insert pos (X ||| 1 <<< a) b hbN
    have hna : (pos ⟨a, haN⟩ : α) ∉ maskSet pos X := by
      rw [mem_maskSet_self]
      simpa using ha
    have hne : (pos ⟨a, haN⟩ : α) ≠ (pos ⟨b, hbN⟩ : α) := by
      intro h
      have h' := pos.injective (Subtype.ext h)
      simp only [Fin.mk.injEq] at h'
      omega
    have hU : maskSet pos (X ||| 1 <<< a ||| 1 <<< b) =
        maskSet pos (X ||| 1 <<< a) ∪ maskSet pos (X ||| 1 <<< b) := by
      rw [hAB, hA, hB]
      ext x
      simp only [mem_insert_iff, mem_union]
      tauto
    have hI : maskSet pos (X ||| 1 <<< a) ∩ maskSet pos (X ||| 1 <<< b) = maskSet pos X := by
      rw [hA, hB]
      ext x
      simp only [mem_insert_iff, mem_inter_iff]
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · exact absurd (h1.symm.trans h2) hne
        · rw [h1] at h2
          exact absurd h2 hna
        · exact h1
        · exact h1
      · intro h
        exact ⟨Or.inr h, Or.inr h⟩
    have h := M.eRk_inter_add_eRk_union_le (maskSet pos (X ||| 1 <<< a))
      (maskSet pos (X ||| 1 <<< b))
    rw [hI, ← hU, ← maskRank_cast hRank pos X,
      ← maskRank_cast hRank pos (X ||| 1 <<< a ||| 1 <<< b),
      ← maskRank_cast hRank pos (X ||| 1 <<< a), ← maskRank_cast hRank pos (X ||| 1 <<< b)] at h
    have h' : maskRank M pos X + maskRank M pos (X ||| 1 <<< a ||| 1 <<< b) ≤
        maskRank M pos (X ||| 1 <<< a) + maskRank M pos (X ||| 1 <<< b) := by
      exact_mod_cast h
    omega
  factT := hfactT
  factF := hfactF
  noCBO := maskRank_noCBO hRank hN pos hno

theorem maskRank_eq {M : Matroid α} {N : ℕ} (pos : Fin N ≃ M.E) {X r : ℕ}
    (h : M.eRk (maskSet pos X) = (r : ℕ∞)) : maskRank M pos X = r := by
  simp [maskRank, h]

/-- The set named by `X` is `Y` when the bits of `X` mark exactly the positions of `Y`. -/
theorem maskSet_eq {M : Matroid α} {N : ℕ} (pos : Fin N ≃ M.E) {X : ℕ} {Y : Set α}
    (hY : Y ⊆ M.E) (h : ∀ p : Fin N, X.testBit p = true ↔ (pos p : α) ∈ Y) :
    maskSet pos X = Y := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (h p).1 hp
  · intro hy
    obtain ⟨p, hp⟩ := pos.surjective ⟨y, hY hy⟩
    refine ⟨p, (h p).2 (by rw [hp]; exact hy), by rw [hp]⟩

/-- Uniform density on 10 elements bounds every rank from below by `densTab10`. -/
theorem densTab10_le {M : Matroid α} (hRank : M.eRank = 4) (pos : Fin 10 ≃ M.E)
    (hDense : UniformlyDenseRatio M 10 4) :
    ∀ X, X < 2 ^ 10 → densTab10.getD (pc 10 X) 0 ≤ maskRank M pos X := by
  intro X _
  have h := hDense (maskSet pos X) (maskSet_subset pos X)
  rw [encard_maskSet, ← maskRank_cast hRank pos X] at h
  have h' : 4 * pc 10 X ≤ 10 * maskRank M pos X := by exact_mod_cast h
  have hpc : pc 10 X ≤ 10 := by
    unfold pc
    exact (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨s, hs⟩ : ∃ s, pc 10 X = s := ⟨_, rfl⟩
  rw [hs] at h' hpc ⊢
  interval_cases s <;> simp [densTab10] <;> omega

/-! ### Numberings that put a given set first -/

section Block

variable {M : Matroid α} {A : Set α} {a b : ℕ} (hAE : A ⊆ M.E) (aEnum : Fin a ≃ A)
  (bEnum : Fin b ≃ (M.E \ A : Set α))

/-- Position `p < a` names `aEnum p`, and position `a + i` names `bEnum i`. -/
noncomputable def blockFun (p : Fin (a + b)) : M.E :=
  if h : p.val < a then ⟨aEnum ⟨p, h⟩, hAE (aEnum _).2⟩
  else ⟨bEnum ⟨p - a, by have := p.isLt; omega⟩, (bEnum _).2.1⟩

theorem blockFun_lt (p : Fin (a + b)) (h : p.val < a) :
    (blockFun hAE aEnum bEnum p : α) = aEnum ⟨p, h⟩ := by
  simp only [blockFun, dif_pos h]

theorem blockFun_ge (p : Fin (a + b)) (h : ¬ p.val < a) :
    (blockFun hAE aEnum bEnum p : α) = bEnum ⟨p - a, by have := p.isLt; omega⟩ := by
  simp only [blockFun, dif_neg h]

theorem blockFun_injective : Function.Injective (blockFun hAE aEnum bEnum) := by
  intro p q hpq
  have h' : (blockFun hAE aEnum bEnum p : α) = blockFun hAE aEnum bEnum q :=
    congrArg Subtype.val hpq
  by_cases hp : p.val < a <;> by_cases hq : q.val < a
  · rw [blockFun_lt hAE aEnum bEnum p hp, blockFun_lt hAE aEnum bEnum q hq] at h'
    have := aEnum.injective (Subtype.ext h')
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · rw [blockFun_lt hAE aEnum bEnum p hp, blockFun_ge hAE aEnum bEnum q hq] at h'
    have h1 := (aEnum ⟨p, hp⟩).2
    rw [h'] at h1
    exact absurd h1 (bEnum _).2.2
  · rw [blockFun_ge hAE aEnum bEnum p hp, blockFun_lt hAE aEnum bEnum q hq] at h'
    have h1 := (aEnum ⟨q, hq⟩).2
    rw [← h'] at h1
    exact absurd h1 (bEnum _).2.2
  · rw [blockFun_ge hAE aEnum bEnum p hp, blockFun_ge hAE aEnum bEnum q hq] at h'
    have := bEnum.injective (Subtype.ext h')
    have h2 := congrArg Fin.val this
    simp only at h2
    exact Fin.ext (by omega)

theorem blockFun_surjective : Function.Surjective (blockFun hAE aEnum bEnum) := by
  intro y
  by_cases hy : (y : α) ∈ A
  · refine ⟨⟨aEnum.symm ⟨y, hy⟩, by have := (aEnum.symm ⟨y, hy⟩).isLt; omega⟩, ?_⟩
    apply Subtype.ext
    rw [blockFun_lt hAE aEnum bEnum _ (aEnum.symm ⟨y, hy⟩).isLt]
    simp
  · have hyd : (y : α) ∈ M.E \ A := ⟨y.2, hy⟩
    refine ⟨⟨bEnum.symm ⟨y, hyd⟩ + a, by have := (bEnum.symm ⟨y, hyd⟩).isLt; omega⟩, ?_⟩
    apply Subtype.ext
    rw [blockFun_ge hAE aEnum bEnum _ (by simp)]
    simp

/-- The block numbering, as an equivalence. -/
noncomputable def blockEquiv : Fin (a + b) ≃ M.E :=
  Equiv.ofBijective _ ⟨blockFun_injective hAE aEnum bEnum, blockFun_surjective hAE aEnum bEnum⟩

theorem blockEquiv_mem_iff (p : Fin (a + b)) :
    (blockEquiv hAE aEnum bEnum p : α) ∈ A ↔ p.val < a := by
  show (blockFun hAE aEnum bEnum p : α) ∈ A ↔ p.val < a
  by_cases h : p.val < a
  · rw [blockFun_lt hAE aEnum bEnum p h]
    exact iff_of_true (aEnum _).2 h
  · rw [blockFun_ge hAE aEnum bEnum p h]
    exact iff_of_false (bEnum _).2.2 h

end Block

/-- The complement of a set of `a` elements in a ground set of `a + b` elements. -/
theorem encard_diff_eq {M : Matroid α} {A : Set α} {a b : ℕ} (hE : M.E.Finite) (hAE : A ⊆ M.E)
    (hEcard : M.E.encard = ((a + b : ℕ) : ℕ∞)) (hAcard : A.encard = (a : ℕ∞)) :
    (M.E \ A).encard = (b : ℕ∞) := by
  have h := Set.encard_sdiff_add_encard_of_subset hAE
  have hfin : (M.E \ A).Finite := hE.subset diff_subset
  rw [hEcard, hAcard, ← hfin.cast_ncard_eq] at h
  rw [← hfin.cast_ncard_eq]
  have h' : (M.E \ A).ncard + a = a + b := by exact_mod_cast h
  have hb : (M.E \ A).ncard = b := by omega
  rw [hb]

/-- Adding an element outside a flat raises its rank by one. -/
theorem eRk_insert_of_isFlat {M : Matroid α} {F : Set α} (hF : M.IsFlat F) {e : α}
    (he : e ∈ M.E) (heF : e ∉ F) : M.eRk (insert e F) = M.eRk F + 1 :=
  M.eRk_insert_eq_add_one ⟨he, by rwa [hF.closure]⟩

/-! ### The base lemmas and the light case -/

/-- **Base lemma of Theorem G**, from its certificate for `r(C) = c`. -/
theorem cbo_of_basePlane {c : ℕ}
    (hcert : ∀ m : RankModelF 10 densTab10 (factsOfRanks (ranksG c)), False)
    {M : Matroid α} (hE : M.E.Finite) (hRank : M.eRank = 4)
    (hEcard : M.E.encard = ((6 + 4 : ℕ) : ℕ∞)) (hDense : UniformlyDenseRatio M 10 4)
    {K : Set α} (hKflat : M.IsFlat K) (hKrank : M.eRk K = 3)
    (hKcard : K.encard = ((6 : ℕ) : ℕ∞)) (hC : M.eRk (M.E \ K) = (c : ℕ∞)) :
    ∃ τ : Fin 10 ≃ M.E, CyclicBasisOrder M 4 (by norm_num) τ := by
  by_contra hno
  have hKE : K ⊆ M.E := hKflat.subset_ground
  let aEnum : Fin 6 ≃ K := finEquivOfSetEncard (hE.subset hKE) hKcard
  let bEnum : Fin 4 ≃ (M.E \ K : Set α) :=
    finEquivOfSetEncard (hE.subset diff_subset) (encard_diff_eq hE hKE hEcard hKcard)
  let pos : Fin 10 ≃ M.E := blockEquiv hKE aEnum bEnum
  have hmem : ∀ p : Fin 10, (pos p : α) ∈ K ↔ (p : ℕ) < 6 := blockEquiv_mem_iff hKE aEnum bEnum
  have hmemC : ∀ p : Fin 10, (pos p : α) ∈ M.E \ K ↔ ¬ (p : ℕ) < 6 := fun p =>
    ⟨fun h => (hmem p).not.1 h.2, fun h => ⟨(pos p).2, (hmem p).not.2 h⟩⟩
  have hK : maskSet pos 63 = K := maskSet_eq pos hKE fun p => by
    rw [hmem p]
    revert p
    decide
  have hC' : maskSet pos 960 = M.E \ K := maskSet_eq pos diff_subset fun p => by
    rw [hmemC p]
    revert p
    decide
  have hins : ∀ x, 6 ≤ x → (hx : x < 10) → M.eRk (maskSet pos (63 ||| 1 <<< x)) = 4 := by
    intro x h6 hx
    have hxK : (pos ⟨x, hx⟩ : α) ∉ K := by
      rw [hmem]
      show ¬ x < 6
      omega
    rw [maskSet_insert pos 63 x hx, hK, eRk_insert_of_isFlat hKflat (pos _).2 hxK, hKrank]
    norm_num
  have hranks : ∀ X s, (X, s) ∈ ranksG c → maskRank M pos X = s := by
    intro X s h
    simp only [ranksG, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · exact maskRank_eq pos (by rw [hK]; exact_mod_cast hKrank)
    · exact maskRank_eq pos (by exact_mod_cast hins 6 (by norm_num) (by norm_num))
    · exact maskRank_eq pos (by exact_mod_cast hins 7 (by norm_num) (by norm_num))
    · exact maskRank_eq pos (by exact_mod_cast hins 8 (by norm_num) (by norm_num))
    · exact maskRank_eq pos (by exact_mod_cast hins 9 (by norm_num) (by norm_num))
    · exact maskRank_eq pos (by rw [hC']; exact hC)
    · simp at h
  exact hcert (rankModelF_of_pos hRank (by norm_num) pos (densTab10_le hRank pos hDense)
    (factT_of_ranks hranks) (factF_of_ranks hranks) hno)

/-- **Base lemma of Theorem L4**, from its certificate. -/
theorem cbo_of_baseLine
    (hcert : ∀ m : RankModelF 10 densTab10 (factsOfRanks ranksL4), False)
    {M : Matroid α} (hE : M.E.Finite) (hRank : M.eRank = 4)
    (hEcard : M.E.encard = ((4 + 6 : ℕ) : ℕ∞)) (hDense : UniformlyDenseRatio M 10 4)
    {L : Set α} (hLflat : M.IsFlat L) (hLrank : M.eRk L = 2)
    (hLcard : L.encard = ((4 : ℕ) : ℕ∞)) :
    ∃ τ : Fin 10 ≃ M.E, CyclicBasisOrder M 4 (by norm_num) τ := by
  by_contra hno
  have hLE : L ⊆ M.E := hLflat.subset_ground
  let aEnum : Fin 4 ≃ L := finEquivOfSetEncard (hE.subset hLE) hLcard
  let bEnum : Fin 6 ≃ (M.E \ L : Set α) :=
    finEquivOfSetEncard (hE.subset diff_subset) (encard_diff_eq hE hLE hEcard hLcard)
  let pos : Fin 10 ≃ M.E := blockEquiv hLE aEnum bEnum
  have hmem : ∀ p : Fin 10, (pos p : α) ∈ L ↔ (p : ℕ) < 4 := blockEquiv_mem_iff hLE aEnum bEnum
  have hL : maskSet pos 15 = L := maskSet_eq pos hLE fun p => by
    rw [hmem p]
    revert p
    decide
  have hins : ∀ x, 4 ≤ x → (hx : x < 10) → M.eRk (maskSet pos (15 ||| 1 <<< x)) = 3 := by
    intro x h4 hx
    have hxL : (pos ⟨x, hx⟩ : α) ∉ L := by
      rw [hmem]
      show ¬ x < 4
      omega
    rw [maskSet_insert pos 15 x hx, hL, eRk_insert_of_isFlat hLflat (pos _).2 hxL, hLrank]
    norm_num
  have hranks : ∀ X s, (X, s) ∈ ranksL4 → maskRank M pos X = s := by
    intro X s h
    simp only [ranksL4, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | h
    · exact maskRank_eq pos (by rw [hL]; exact_mod_cast hLrank)
    · exact maskRank_eq pos (by exact_mod_cast hins 4 (by norm_num) (by norm_num))
    · exact maskRank_eq pos (by exact_mod_cast hins 5 (by norm_num) (by norm_num))
    · exact maskRank_eq pos (by exact_mod_cast hins 6 (by norm_num) (by norm_num))
    · exact maskRank_eq pos (by exact_mod_cast hins 7 (by norm_num) (by norm_num))
    · exact maskRank_eq pos (by exact_mod_cast hins 8 (by norm_num) (by norm_num))
    · exact maskRank_eq pos (by exact_mod_cast hins 9 (by norm_num) (by norm_num))
    · simp at h
  exact hcert (rankModelF_of_pos hRank (by norm_num) pos (densTab10_le hRank pos hDense)
    (factT_of_ranks hranks) (factF_of_ranks hranks) hno)

/-- In the strict t=0 profile, a closure with `j k` elements (the most allowed) is a flat of
rank `j` and size `j k`. -/
theorem closure_of_ncard_eq {M : Matroid α} {k : ℕ} (hT : Hitting.StrictT0 M k) {Y : Set α}
    (hYE : Y ⊆ M.E) {j : ℕ} (hj : M.eRk Y = j) (hj3 : j ≤ 3) (hY : Y.ncard = j * k) :
    M.IsFlat (M.closure Y) ∧ M.eRk (M.closure Y) = j ∧
      (M.closure Y).encard = ((j * k : ℕ) : ℕ∞) := by
  have hclE : M.closure Y ⊆ M.E := M.closure_subset_ground Y
  have hclfin : (M.closure Y).Finite := hT.finite.subset hclE
  have hclrk : M.eRk (M.closure Y) = j := by rw [M.eRk_closure_eq, hj]
  have hle := hT.ncard_le hclE hclrk hj3
  have hge : Y.ncard ≤ (M.closure Y).ncard := Set.ncard_le_ncard (M.subset_closure Y hYE) hclfin
  refine ⟨M.isFlat_closure Y, hclrk, ?_⟩
  rw [← hclfin.cast_ncard_eq]
  have : (M.closure Y).ncard = j * k := by omega
  rw [this]

/-- In the strict t=0 class on 10 elements with no 6-plane and no 4-line, `lightTab10` bounds
every rank from below. -/
theorem lightTab10_le {M : Matroid α} (hT : Hitting.StrictT0 M 2) (pos : Fin 10 ≃ M.E)
    (h6 : ∀ F, M.IsFlat F → M.eRk F = 3 → F.encard ≠ ((3 * 2 : ℕ) : ℕ∞))
    (h4 : ∀ F, M.IsFlat F → M.eRk F = 2 → F.encard ≠ ((2 * 2 : ℕ) : ℕ∞)) :
    ∀ X, X < 2 ^ 10 → lightTab10.getD (pc 10 X) 0 ≤ maskRank M pos X := by
  intro X _
  have hYE : maskSet pos X ⊆ M.E := maskSet_subset pos X
  have hYfin : (maskSet pos X).Finite := hT.finite.subset hYE
  have hYcard : (maskSet pos X).ncard = pc 10 X := by
    have h := encard_maskSet pos X
    rw [← hYfin.cast_ncard_eq] at h
    exact_mod_cast h
  obtain ⟨j, hj, hj4⟩ := hT.exists_eRk_eq (maskSet pos X)
  rw [maskRank_eq pos hj, ← hYcard]
  have hpc : (maskSet pos X).ncard ≤ 10 := by
    rw [hYcard]
    unfold pc
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hle : j ≤ 3 → (maskSet pos X).ncard ≤ j * 2 := fun hj3 => hT.ncard_le hYE hj hj3
  have hno4 : j = 2 → (maskSet pos X).ncard ≠ 4 := by
    rintro rfl hY
    obtain ⟨hfl, hrk, hcard⟩ := closure_of_ncard_eq hT hYE hj (by norm_num) (by omega)
    exact h4 _ hfl (by exact_mod_cast hrk) hcard
  have hno6 : j = 3 → (maskSet pos X).ncard ≠ 6 := by
    rintro rfl hY
    obtain ⟨hfl, hrk, hcard⟩ := closure_of_ncard_eq hT hYE hj (by norm_num) (by omega)
    exact h6 _ hfl (by exact_mod_cast hrk) hcard
  have hlight : ∀ s ≤ 10, lightTab10.getD s 0 =
      if s = 0 then 0 else if s ≤ 2 then 1 else if s = 3 then 2 else if s ≤ 5 then 3 else 4 := by
    decide
  rw [hlight _ hpc]
  split_ifs <;> omega

/-- **KUM(4,10) in the strict t=0 class with no 6-plane and no 4-line**, from its certificate. -/
theorem cbo_of_light (hcert : ∀ m : RankModelF 10 lightTab10 [], False)
    {M : Matroid α} (hT : Hitting.StrictT0 M 2)
    (h6 : ∀ F, M.IsFlat F → M.eRk F = 3 → F.encard ≠ ((3 * 2 : ℕ) : ℕ∞))
    (h4 : ∀ F, M.IsFlat F → M.eRk F = 2 → F.encard ≠ ((2 * 2 : ℕ) : ℕ∞)) :
    ∃ τ : Fin 10 ≃ M.E, CyclicBasisOrder M 4 (by norm_num) τ := by
  by_contra hno
  let pos : Fin 10 ≃ M.E := finEquivGround hT.finite (hT.card.trans (by norm_num))
  exact hcert (rankModelF_of_pos hT.rank (by norm_num) pos (lightTab10_le hT pos h6 h4)
    (fun X v h => by cases h) (fun X v h => by cases h) hno)

end Probe.Enc
