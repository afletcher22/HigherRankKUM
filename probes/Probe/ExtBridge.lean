import Probe.ExtEnc
import Probe.EncBridge
import Probe.Rank4.TheoremD

/-!
# From extension certificates to the rank-4 extension theorem

Let `S` be a basis of a rank-4 matroid `M`, and `σ` a cyclic ordering of the other `N` elements
whose 4-windows are bases. Number the ground set by positions: `0..3` for `S`, and `4 + i` for
`σ i`. If `M` had no cyclic basis ordering, the ranks of the sets named by bitmasks would form a
`RankModelX`:

* every basis clause holds, because `S` and each window of `σ` are bases;
* every admissible merged sequence has some `S`-window of rank below `4`, since otherwise it would
  give a cyclic basis ordering of `M`.

A cyclic certificate uses all `N + 4` positions (`rank4Extension_of_cert`).

A linear certificate of length `L ≤ N` uses only the positions of `S` and `e_0, …, e_{L-1}`
(`rank4Extension_of_linCert`). An admissible merged sequence `q` of these positions starts with
`e_0, e_1, e_2` and ends with `e_{L-3}, e_{L-2}, e_{L-1}`. Follow `q` by `e_L, …, e_{N-1}` to get a
cyclic ordering of `M`. Each of its windows is either a window of `q` or a window of `σ`.
-/

namespace Probe.Enc

open Set HigherRankKUM
open scoped Matroid

variable {α : Type*}

/-- A numbering of a finite set of known size. -/
noncomputable def finEquivOfSetEncard {S : Set α} {n : ℕ} (hS : S.Finite)
    (h : S.encard = (n : ℕ∞)) : Fin n ≃ S := by
  haveI : Finite S := hS.to_subtype
  have hn : S.ncard = n := by
    have hcast : (S.ncard : ℕ∞) = n := by
      rw [hS.cast_ncard_eq]
      exact h
    exact_mod_cast hcast
  exact (Finite.equivFinOfCardEq (by simpa only [Nat.card_coe_set_eq] using hn)).symm

theorem testBit_ewin (N i x : ℕ) :
    ((List.range 4).foldl (fun acc t => acc ||| 1 <<< (4 + (i + t) % N)) 0).testBit x = true ↔
      ∃ t < 4, 4 + (i + t) % N = x := by
  rw [testBit_foldl_or (fun t => 4 + (i + t) % N) x (List.range 4) 0]
  simp [List.mem_range]

theorem testBit_lwin (i x : ℕ) :
    ((List.range 4).foldl (fun acc t => acc ||| 1 <<< (4 + i + t)) 0).testBit x = true ↔
      ∃ t < 4, 4 + i + t = x := by
  rw [testBit_foldl_or (fun t => 4 + i + t) x (List.range 4) 0]
  simp [List.mem_range]

theorem pc_eq_of_lt {m n X : ℕ} (hnm : n ≤ m) (hX : X < 2 ^ n) : pc m X = pc n X := by
  unfold pc
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hb⟩
    refine ⟨?_, hb⟩
    by_contra h
    have h0 : X.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [h0] at hb
  · rintro ⟨hj, hb⟩
    exact ⟨by omega, hb⟩

/-! ### Rank models from a numbering of the ground set -/

/-- The rank in `M` of the set named by the bitmask `X`. -/
noncomputable def maskRank (M : Matroid α) {m : ℕ} (pos : Fin m ≃ M.E) (X : ℕ) : ℕ :=
  (M.eRk (maskSet pos X)).toNat

theorem maskRank_cast {M : Matroid α} (hRank : M.eRank = 4) {m : ℕ} (pos : Fin m ≃ M.E)
    (X : ℕ) : ((maskRank M pos X : ℕ) : ℕ∞) = M.eRk (maskSet pos X) :=
  ENat.coe_toNat (ne_top_of_le_ne_top (by rw [hRank]; exact ENat.coe_ne_top 4)
    (M.eRk_le_eRank _))

theorem four_le_maskRank {M : Matroid α} (hRank : M.eRank = 4) {m : ℕ} (pos : Fin m ≃ M.E)
    {X : ℕ} {B : Set α} (hB : B ⊆ maskSet pos X) (hBase : M.IsBase B) :
    4 ≤ maskRank M pos X := by
  have h := M.eRk_mono hB
  rw [hBase.indep.eRk_eq_encard, hBase.encard_eq_eRank, hRank, ← maskRank_cast hRank pos X] at h
  exact_mod_cast h

/-- The ranks of the sets named by bitmasks over the first `n` of `m` positions form a rank model,
given its basis and interleaving properties. -/
noncomputable def rankModelX_of_pos {M : Matroid α} (hRank : M.eRank = 4) {m n : ℕ}
    (hnm : n ≤ m) (pos : Fin m ≃ M.E) {cyc : Bool} {bases : List ℕ}
    (hbase : ∀ X ∈ bases, 4 ≤ maskRank M pos X)
    (hnoExt : ∀ q, interOK n cyc bases q →
      ∃ j ∈ (starts cyc q).filter (hasS q), maskRank M pos (window q j) < 4) :
    RankModelX n cyc bases where
  r := maskRank M pos
  card X hX := by
    have h := M.eRk_le_encard (maskSet pos X)
    rw [← maskRank_cast hRank pos X, encard_maskSet, pc_eq_of_lt hnm hX] at h
    exact_mod_cast h
  mono X a _ ha _ := by
    have ha' : a < m := by omega
    have h := M.eRk_mono (show maskSet pos X ⊆ maskSet pos (X ||| 1 <<< a) by
      rw [maskSet_insert pos X a ha']
      exact subset_insert _ _)
    rw [← maskRank_cast hRank pos X, ← maskRank_cast hRank pos (X ||| 1 <<< a)] at h
    exact_mod_cast h
  ins X a _ ha _ := by
    have ha' : a < m := by omega
    have h := M.eRk_insert_le_add_one (pos ⟨a, ha'⟩ : α) (maskSet pos X)
    rw [← maskSet_insert pos X a ha', ← maskRank_cast hRank pos X,
      ← maskRank_cast hRank pos (X ||| 1 <<< a)] at h
    exact_mod_cast h
  sub X a b _ hab hbN ha hb := by
    have hbm : b < m := by omega
    have ham : a < m := by omega
    have hA := maskSet_insert pos X a ham
    have hB := maskSet_insert pos X b hbm
    have hAB := maskSet_insert pos (X ||| 1 <<< a) b hbm
    have hna : (pos ⟨a, ham⟩ : α) ∉ maskSet pos X := by
      rw [mem_maskSet_self]
      simpa using ha
    have hne : (pos ⟨a, ham⟩ : α) ≠ (pos ⟨b, hbm⟩ : α) := by
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
  base := hbase
  noExt := hnoExt

/-- A cyclic window of rank at least `4` in a rank-4 matroid is a basis. -/
theorem isBase_cyclicWindow_of_four_le {M : Matroid α} (hRank : M.eRank = 4) {n : ℕ}
    (hn : 0 < n) (τ : Fin n ≃ M.E) (j : Fin n)
    (h4 : (4 : ℕ∞) ≤ M.eRk (cyclicWindow 4 hn τ j)) : M.IsBase (cyclicWindow 4 hn τ j) := by
  have hWfin : (cyclicWindow 4 hn τ j).Finite := Set.finite_range _
  have hWcard : (cyclicWindow 4 hn τ j).encard ≤ 4 := by
    rw [cyclicWindow, ← Set.image_univ]
    exact (Set.encard_image_le _ _).trans (by simp)
  have hind : M.Indep (cyclicWindow 4 hn τ j) :=
    (Matroid.indep_iff_eRk_eq_encard_of_finite (M := M) hWfin).2
      (le_antisymm (M.eRk_le_encard _) (hWcard.trans h4))
  exact hind.isBase_of_eRk_ge hWfin (by rw [hRank]; exact h4)

/-! ### The numbering by positions -/

section Numbering

variable {M : Matroid α} {S : Set α} {N : ℕ} (hSE : S ⊆ M.E) (sEnum : Fin 4 ≃ S)
  (σ : Fin N ≃ (M.E \ S : Set α))

/-- Position `p < 4` names `sEnum p`, and position `4 + i` names `σ i`. -/
noncomputable def posFun (p : Fin (N + 4)) : M.E :=
  if h : p.val < 4 then ⟨sEnum ⟨p, h⟩, hSE (sEnum _).2⟩
  else ⟨σ ⟨p - 4, by have := p.isLt; omega⟩, (σ _).2.1⟩

theorem posFun_lt (p : Fin (N + 4)) (h : p.val < 4) :
    (posFun hSE sEnum σ p : α) = sEnum ⟨p, h⟩ := by
  simp only [posFun, dif_pos h]

theorem posFun_ge (p : Fin (N + 4)) (h : ¬ p.val < 4) :
    (posFun hSE sEnum σ p : α) = σ ⟨p - 4, by have := p.isLt; omega⟩ := by
  simp only [posFun, dif_neg h]

theorem posFun_injective : Function.Injective (posFun hSE sEnum σ) := by
  intro a b hab
  have hab' : (posFun hSE sEnum σ a : α) = posFun hSE sEnum σ b := congrArg Subtype.val hab
  by_cases ha : a.val < 4 <;> by_cases hb : b.val < 4
  · rw [posFun_lt hSE sEnum σ a ha, posFun_lt hSE sEnum σ b hb] at hab'
    have := sEnum.injective (Subtype.ext hab')
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · rw [posFun_lt hSE sEnum σ a ha, posFun_ge hSE sEnum σ b hb] at hab'
    exact absurd (hab' ▸ (sEnum _).2) (σ _).2.2
  · rw [posFun_ge hSE sEnum σ a ha, posFun_lt hSE sEnum σ b hb] at hab'
    have h1 := (sEnum ⟨b, hb⟩).2
    rw [← hab'] at h1
    exact absurd h1 (σ _).2.2
  · rw [posFun_ge hSE sEnum σ a ha, posFun_ge hSE sEnum σ b hb] at hab'
    have := σ.injective (Subtype.ext hab')
    have h2 := congrArg Fin.val this
    simp only at h2
    exact Fin.ext (by omega)

theorem posFun_surjective : Function.Surjective (posFun hSE sEnum σ) := by
  intro y
  by_cases hy : (y : α) ∈ S
  · refine ⟨⟨sEnum.symm ⟨y, hy⟩, by have := (sEnum.symm ⟨y, hy⟩).isLt; omega⟩, ?_⟩
    apply Subtype.ext
    rw [posFun_lt hSE sEnum σ _ (sEnum.symm ⟨y, hy⟩).isLt]
    simp
  · have hyd : (y : α) ∈ M.E \ S := ⟨y.2, hy⟩
    refine ⟨⟨σ.symm ⟨y, hyd⟩ + 4, by have := (σ.symm ⟨y, hyd⟩).isLt; omega⟩, ?_⟩
    apply Subtype.ext
    rw [posFun_ge hSE sEnum σ _ (by simp)]
    simp

/-- The numbering by positions, as an equivalence. -/
noncomputable def posEquiv : Fin (N + 4) ≃ M.E :=
  Equiv.ofBijective _ ⟨posFun_injective hSE sEnum σ, posFun_surjective hSE sEnum σ⟩

theorem posEquiv_apply (p : Fin (N + 4)) :
    posEquiv hSE sEnum σ p = posFun hSE sEnum σ p := rfl

theorem subset_maskSet_S : S ⊆ maskSet (posEquiv hSE sEnum σ) 15 := by
  intro s hs
  refine ⟨⟨sEnum.symm ⟨s, hs⟩, by have := (sEnum.symm ⟨s, hs⟩).isLt; omega⟩, ?_, ?_⟩
  · have := (sEnum.symm ⟨s, hs⟩).isLt
    interval_cases h : (sEnum.symm ⟨s, hs⟩ : ℕ) <;> decide
  · rw [posEquiv_apply, posFun_lt hSE sEnum σ _ (sEnum.symm ⟨s, hs⟩).isLt]
    simp

theorem subset_maskSet_ewin (hN : 0 < N) (i : ℕ) (hi : i < N) :
    cyclicWindow 4 hN σ ⟨i, hi⟩ ⊆ maskSet (posEquiv hSE sEnum σ)
      ((List.range 4).foldl (fun acc t => acc ||| 1 <<< (4 + (i + t) % N)) 0) := by
  rintro x ⟨t, rfl⟩
  refine ⟨⟨4 + (i + t) % N, by have := Nat.mod_lt (i + t) hN; omega⟩, ?_, ?_⟩
  · exact (testBit_ewin N i _).2 ⟨t, t.isLt, rfl⟩
  · rw [posEquiv_apply, posFun_ge hSE sEnum σ _ (by simp)]
    simp [cyclicIndex]

theorem subset_maskSet_lwin (hN : 0 < N) (i : ℕ) (hi : i + 4 ≤ N) :
    cyclicWindow 4 hN σ ⟨i, by omega⟩ ⊆ maskSet (posEquiv hSE sEnum σ)
      ((List.range 4).foldl (fun acc t => acc ||| 1 <<< (4 + i + t)) 0) := by
  rintro x ⟨t, rfl⟩
  have ht := t.isLt
  refine ⟨⟨4 + (i + t), by omega⟩, ?_, ?_⟩
  · exact (testBit_lwin i _).2 ⟨t, ht, Nat.add_assoc 4 i t⟩
  · rw [posEquiv_apply, posFun_ge hSE sEnum σ _ (by simp)]
    simp [cyclicIndex, Nat.mod_eq_of_lt (show i + (t : ℕ) < N by omega)]

end Numbering

/-! ### The bridges -/

/-- **The rank-4 extension theorem on `N` elements, from a cyclic certificate.** -/
theorem rank4Extension_of_cert {N : ℕ} (hN0 : 0 < N)
    (hcert : ∀ m : RankModelX (N + 4) true (basesCyc N), False) : Rank4Extension α N := by
  intro M S hN hE hRank hS hσex
  obtain ⟨σ, hσ⟩ := hσex
  by_contra hno
  have hSE : S ⊆ M.E := hS.subset_ground
  have hScard : S.encard = ((4 : ℕ) : ℕ∞) := by rw [hS.encard_eq_eRank, hRank]; rfl
  let sEnum : Fin 4 ≃ S := finEquivOfSetEncard (hE.subset hSE) hScard
  let pos := posEquiv hSE sEnum σ
  have hbC : ∀ X ∈ basesCyc N, 4 ≤ maskRank M pos X := by
    intro X hX
    simp only [basesCyc, List.mem_cons, List.mem_map, List.mem_range] at hX
    rcases hX with rfl | ⟨i, hi, rfl⟩
    · exact four_le_maskRank hRank pos (subset_maskSet_S hSE sEnum σ) hS
    · exact four_le_maskRank hRank pos (subset_maskSet_ewin hSE sEnum σ hN i hi) (hσ ⟨i, hi⟩)
  refine hcert (rankModelX_of_pos hRank (Nat.le_refl _) pos hbC ?_)
  -- no admissible merged sequence works
  intro q hq
  obtain ⟨hlen, hcov, hbound, hfree, -⟩ := hq
  by_contra hall
  push_neg at hall
  have hwin : ∀ j < q.length, 4 ≤ maskRank M pos (window q j) := by
    intro j hj
    have hjs : j ∈ starts true q := by simpa [starts] using hj
    by_cases hS' : hasS q j = true
    · exact hall j (List.mem_filter.2 ⟨hjs, hS'⟩)
    · exact hbC _ (hfree j hjs (by simpa using hS'))
  -- the merged sequence is a cyclic basis ordering of `M`
  have hlt : ∀ k : Fin (N + 4), q.getD k 0 < N + 4 := by
    intro k
    apply hbound
    have hk : (k : ℕ) < q.length := by omega
    rw [List.getD_eq_getElem?_getD]
    simp [hk]
  let p : Fin (N + 4) → Fin (N + 4) := fun k => ⟨q.getD k 0, hlt k⟩
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.1 (hcov y y.2)
    refine ⟨⟨k, by omega⟩, Fin.ext ?_⟩
    simp only [p, List.getD_eq_getElem?_getD]
    simp [hk, hky]
  have hpbij : Function.Bijective p := ⟨Finite.injective_iff_surjective.2 hpsurj, hpsurj⟩
  let τ : Fin (N + 4) ≃ M.E := (Equiv.ofBijective p hpbij).trans pos
  refine hno ⟨τ, fun j => isBase_cyclicWindow_of_four_le hRank (by omega) τ j ?_⟩
  have hsub : maskSet pos (window q j) ⊆ cyclicWindow 4 (by omega) τ j := by
    rintro x ⟨k, hk, rfl⟩
    rw [testBit_window, hlen] at hk
    obtain ⟨t, ht, htk⟩ := hk
    rw [cyclicWindow, Set.mem_range]
    refine ⟨⟨t, ht⟩, ?_⟩
    have hpk : p (cyclicIndex (N + 4) (by omega) j t) = k :=
      Fin.ext (by simpa [p, cyclicIndex] using htk)
    simp [τ, hpk]
  have h2 := M.eRk_mono hsub
  rw [← maskRank_cast hRank pos] at h2
  calc (4 : ℕ∞) ≤ ((maskRank M pos (window q j) : ℕ) : ℕ∞) := by
        exact_mod_cast hwin j (by omega)
    _ ≤ M.eRk (cyclicWindow 4 (by omega) τ j) := h2

/-- **The rank-4 extension theorem on `N ≥ L` elements, from a linear certificate of length
`L`.** -/
theorem rank4Extension_of_linCert {L N : ℕ} (hL : 3 ≤ L) (hLN : L ≤ N)
    (hcert : ∀ m : RankModelX (L + 4) false (basesLin L), False) : Rank4Extension α N := by
  intro M S hN hE hRank hS hσex
  obtain ⟨σ, hσ⟩ := hσex
  by_contra hno
  have hSE : S ⊆ M.E := hS.subset_ground
  have hScard : S.encard = ((4 : ℕ) : ℕ∞) := by rw [hS.encard_eq_eRank, hRank]; rfl
  let sEnum : Fin 4 ≃ S := finEquivOfSetEncard (hE.subset hSE) hScard
  let pos := posEquiv hSE sEnum σ
  have hN4 : 0 < N + 4 := by omega
  have hbL : ∀ X ∈ basesLin L, 4 ≤ maskRank M pos X := by
    intro X hX
    simp only [basesLin, List.mem_cons, List.mem_map, List.mem_range] at hX
    rcases hX with rfl | ⟨i, hi, rfl⟩
    · exact four_le_maskRank hRank pos (subset_maskSet_S hSE sEnum σ) hS
    · exact four_le_maskRank hRank pos (subset_maskSet_lwin hSE sEnum σ hN i (by omega))
        (hσ _)
  refine hcert (rankModelX_of_pos hRank (by omega) pos hbL ?_)
  -- no admissible merged sequence works
  intro q hq
  obtain ⟨hlen, hcov, hbound, hfree, hends⟩ := hq
  by_contra hall
  push_neg at hall
  -- every window of `q` has rank `4`
  have hwin : ∀ j, j ≤ L → 4 ≤ maskRank M pos (window q j) := by
    intro j hj
    have hjs : j ∈ starts false q := by
      show j ∈ List.range (q.length - 3)
      rw [List.mem_range, hlen]
      omega
    by_cases hS' : hasS q j = true
    · exact hall j (List.mem_filter.2 ⟨hjs, hS'⟩)
    · exact hbL _ (hfree j hjs (by simpa using hS'))
  -- `q` starts with `e_0, e_1, e_2` and ends with `e_{L-3}, e_{L-2}, e_{L-1}`
  have hq_lo : ∀ k < 3, q.getD k 0 = k + 4 := fun k hk => (hends rfl k hk).1
  have hq_hi : ∀ k, L + 1 ≤ k → k < L + 4 → q.getD k 0 = k := by
    intro k hk1 hk2
    have h := (hends rfl (k - (L + 1)) (by omega)).2
    have e : L + 4 - 3 + (k - (L + 1)) = k := by omega
    rw [e] at h
    exact h
  -- the merged sequence, followed by `e_L, …, e_{N-1}`
  have hget : ∀ k, k < L + 4 → q.getD k 0 ∈ q := by
    intro k hk
    have hk' : k < q.length := by omega
    rw [List.getD_eq_getElem?_getD]
    simp [hk']
  let p : Fin (N + 4) → Fin (N + 4) := fun c =>
    if h : (c : ℕ) < L + 4 then ⟨q.getD c 0, by have := hbound _ (hget c h); omega⟩ else c
  have hp_lt : ∀ c : Fin (N + 4), (c : ℕ) < L + 4 → (p c : ℕ) = q.getD c 0 := by
    intro c hc
    simp only [p, dif_pos hc]
  have hp_ge : ∀ c : Fin (N + 4), L + 4 ≤ (c : ℕ) → p c = c := by
    intro c hc
    simp only [p, dif_neg (show ¬ (c : ℕ) < L + 4 by omega)]
  have hp_lo : ∀ c : Fin (N + 4), (c : ℕ) < 3 → (p c : ℕ) = c + 4 := by
    intro c hc
    rw [hp_lt c (by omega), hq_lo c hc]
  have hp_hi : ∀ c : Fin (N + 4), L + 1 ≤ (c : ℕ) → (p c : ℕ) = c := by
    intro c hc
    by_cases h : (c : ℕ) < L + 4
    · rw [hp_lt c h, hq_hi c hc h]
    · rw [hp_ge c (by omega)]
  have hpsurj : Function.Surjective p := by
    intro y
    by_cases hy : (y : ℕ) < L + 4
    · obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.1 (hcov y hy)
      refine ⟨⟨k, by omega⟩, Fin.ext ?_⟩
      rw [hp_lt ⟨k, by omega⟩ (show k < L + 4 by omega)]
      simp [List.getD_eq_getElem?_getD, hk, hky]
    · exact ⟨y, hp_ge y (by omega)⟩
  have hpbij : Function.Bijective p := ⟨Finite.injective_iff_surjective.2 hpsurj, hpsurj⟩
  let τ : Fin (N + 4) ≃ M.E := (Equiv.ofBijective p hpbij).trans pos
  have hτ : ∀ c, (τ c : α) = posFun hSE sEnum σ (p c) := fun _ => rfl
  have hmod : ∀ a b : ℕ, b ≤ a → a < 2 * b → a % b = a - b := by
    intro a b h1 h2
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  -- every window of `τ` has rank `4`
  have hrk : ∀ j : Fin (N + 4), (4 : ℕ∞) ≤ M.eRk (cyclicWindow 4 hN4 τ j) := by
    intro j
    have hj := j.isLt
    by_cases hjL : (j : ℕ) ≤ L
    · -- a window of `q`
      have hsub : maskSet pos (window q j) ⊆ cyclicWindow 4 hN4 τ j := by
        rintro x ⟨k, hk, rfl⟩
        rw [testBit_window, hlen] at hk
        obtain ⟨t, ht, htk⟩ := hk
        rw [Nat.mod_eq_of_lt (by omega : (j : ℕ) + t < L + 4)] at htk
        rw [cyclicWindow, Set.mem_range]
        refine ⟨⟨t, ht⟩, ?_⟩
        have hcv : (cyclicIndex (N + 4) hN4 j t : ℕ) = j + t := by
          show ((j : ℕ) + t) % (N + 4) = j + t
          exact Nat.mod_eq_of_lt (by omega)
        have hpk : p (cyclicIndex (N + 4) hN4 j t) = k := by
          apply Fin.ext
          rw [hp_lt _ (by omega), hcv, htk]
        show (pos (p (cyclicIndex (N + 4) hN4 j t)) : α) = pos k
        rw [hpk]
      have h2 := M.eRk_mono hsub
      rw [← maskRank_cast hRank pos] at h2
      calc (4 : ℕ∞) ≤ ((maskRank M pos (window q j) : ℕ) : ℕ∞) := by
            exact_mod_cast hwin j hjL
        _ ≤ M.eRk (cyclicWindow 4 hN4 τ j) := h2
    · -- a window of `σ`
      have hsub : cyclicWindow 4 hN σ ⟨(j : ℕ) - 4, by omega⟩ ⊆ cyclicWindow 4 hN4 τ j := by
        rintro x ⟨t, rfl⟩
        have ht := t.isLt
        rw [cyclicWindow, Set.mem_range]
        refine ⟨t, ?_⟩
        have hcv : (cyclicIndex (N + 4) hN4 j t : ℕ) = ((j : ℕ) + t) % (N + 4) := rfl
        have hiv : (cyclicIndex N hN ⟨(j : ℕ) - 4, by omega⟩ t : ℕ) =
            ((j : ℕ) - 4 + t) % N := rfl
        have hpc : (p (cyclicIndex (N + 4) hN4 j t) : ℕ) =
            (cyclicIndex N hN ⟨(j : ℕ) - 4, by omega⟩ t : ℕ) + 4 := by
          by_cases hw : (j : ℕ) + t < N + 4
          · rw [Nat.mod_eq_of_lt hw] at hcv
            rw [Nat.mod_eq_of_lt (by omega : (j : ℕ) - 4 + t < N)] at hiv
            rw [hp_hi _ (by omega), hcv, hiv]
            omega
          · rw [hmod ((j : ℕ) + t) (N + 4) (by omega) (by omega)] at hcv
            rw [hmod ((j : ℕ) - 4 + t) N (by omega) (by omega)] at hiv
            rw [hp_lo _ (by omega), hcv, hiv]
            omega
        rw [hτ, posFun_ge hSE sEnum σ _ (by omega)]
        exact congrArg (fun i => (σ i : α)) (Fin.ext (by simp only [Fin.val_mk]; omega))
      have h2 := M.eRk_mono hsub
      have hB := hσ ⟨(j : ℕ) - 4, by omega⟩
      rw [hB.indep.eRk_eq_encard, hB.encard_eq_eRank, hRank] at h2
      exact h2
  exact hno ⟨τ, fun j => isBase_cyclicWindow_of_four_le hRank hN4 τ j (hrk j)⟩

end Probe.Enc
