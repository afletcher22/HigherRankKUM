import Probe.ExtEnc
import Probe.EncBridge
import Probe.Rank4.TheoremD

/-!
# From extension certificates to the rank-4 extension theorem

Let `S` be a basis and `σ` a cyclic ordering of the other `N` elements whose 4-windows are bases.
Number the ground set by positions: `0..3` for `S`, and `4 + i` for `σ i`. If no cyclic basis
ordering of `M` existed, the ranks of the sets named by bitmasks would form a `RankModelX`:

* every basis clause holds, because `S` and each window of `σ` are bases;
* every admissible merged sequence has some `S`-window of rank below `4`, since otherwise the
  merged sequence would be a cyclic basis ordering of `M`.

So a refutation of `RankModelX (N + 4) true (basesCyc N)` proves `Rank4Extension α N`.
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

/-- **The rank-4 extension theorem on `N` elements, from a cyclic certificate.** -/
theorem rank4Extension_of_cert {N : ℕ} (hN0 : 0 < N)
    (hcert : ∀ m : RankModelX (N + 4) true (basesCyc N), False) : Rank4Extension α N := by
  intro M S hN hE hRank hS hσex
  obtain ⟨σ, hσ⟩ := hσex
  by_contra hno
  have hSE : S ⊆ M.E := hS.subset_ground
  have hSfin : S.Finite := hE.subset hSE
  have hScard : S.encard = ((4 : ℕ) : ℕ∞) := by rw [hS.encard_eq_eRank, hRank]; rfl
  let sEnum : Fin 4 ≃ S := finEquivOfSetEncard hSfin hScard
  -- the numbering of the ground set by positions
  let f : Fin (N + 4) → M.E := fun p =>
    if h : p.val < 4 then ⟨sEnum ⟨p, h⟩, hSE (sEnum _).2⟩
    else ⟨σ ⟨p - 4, by have := p.isLt; omega⟩, (σ _).2.1⟩
  have hf_lt : ∀ (p : Fin (N + 4)) (h : p.val < 4), (f p : α) = sEnum ⟨p, h⟩ := by
    intro p h
    simp only [f, dif_pos h]
  have hf_ge : ∀ (p : Fin (N + 4)) (h : ¬ p.val < 4),
      (f p : α) = σ ⟨p - 4, by have := p.isLt; omega⟩ := by
    intro p h
    simp only [f, dif_neg h]
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' : (f a : α) = f b := congrArg Subtype.val hab
    by_cases ha : a.val < 4 <;> by_cases hb : b.val < 4
    · rw [hf_lt a ha, hf_lt b hb] at hab'
      have := sEnum.injective (Subtype.ext hab')
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · rw [hf_lt a ha, hf_ge b hb] at hab'
      exact absurd (hab' ▸ (sEnum _).2) (σ _).2.2
    · rw [hf_ge a ha, hf_lt b hb] at hab'
      have h1 := (sEnum ⟨b, hb⟩).2
      rw [← hab'] at h1
      exact absurd h1 (σ _).2.2
    · rw [hf_ge a ha, hf_ge b hb] at hab'
      have := σ.injective (Subtype.ext hab')
      have h2 := congrArg Fin.val this
      simp only at h2
      exact Fin.ext (by omega)
  have hsurj : Function.Surjective f := by
    intro y
    by_cases hy : (y : α) ∈ S
    · refine ⟨⟨sEnum.symm ⟨y, hy⟩, by have := (sEnum.symm ⟨y, hy⟩).isLt; omega⟩, ?_⟩
      apply Subtype.ext
      rw [hf_lt _ (sEnum.symm ⟨y, hy⟩).isLt]
      simp
    · have hyd : (y : α) ∈ M.E \ S := ⟨y.2, hy⟩
      refine ⟨⟨σ.symm ⟨y, hyd⟩ + 4, by have := (σ.symm ⟨y, hyd⟩).isLt; omega⟩, ?_⟩
      apply Subtype.ext
      rw [hf_ge _ (by simp)]
      simp
  let pos : Fin (N + 4) ≃ M.E := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hpos : ∀ p, (pos p : α) = f p := fun _ => rfl
  -- ranks of the sets named by bitmasks
  let r : ℕ → ℕ := fun X => (M.eRk (maskSet pos X)).toNat
  have hcast : ∀ X, ((r X : ℕ) : ℕ∞) = M.eRk (maskSet pos X) := fun X =>
    ENat.coe_toNat (ne_top_of_le_ne_top (by rw [hRank]; exact ENat.coe_ne_top 4)
      (M.eRk_le_eRank _))
  have hge4 : ∀ X (B : Set α), B ⊆ maskSet pos X → M.IsBase B → 4 ≤ r X := by
    intro X B hB hBase
    have h := M.eRk_mono hB
    rw [hBase.indep.eRk_eq_encard, hBase.encard_eq_eRank, hRank, ← hcast X] at h
    exact_mod_cast h
  refine hcert ⟨r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _
    have h := M.eRk_le_encard (maskSet pos X)
    rw [← hcast X, encard_maskSet] at h
    exact_mod_cast h
  · intro X a _ ha _
    have h := M.eRk_mono (show maskSet pos X ⊆ maskSet pos (X ||| 1 <<< a) by
      rw [maskSet_insert pos X a ha]
      exact subset_insert _ _)
    rw [← hcast X, ← hcast (X ||| 1 <<< a)] at h
    exact_mod_cast h
  · intro X a _ ha _
    have h := M.eRk_insert_le_add_one (pos ⟨a, ha⟩ : α) (maskSet pos X)
    rw [← maskSet_insert pos X a ha, ← hcast X, ← hcast (X ||| 1 <<< a)] at h
    exact_mod_cast h
  · intro X a b _ hab hbN ha hb
    have haN : a < N + 4 := by omega
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
    rw [hI, ← hU, ← hcast X, ← hcast (X ||| 1 <<< a ||| 1 <<< b), ← hcast (X ||| 1 <<< a),
      ← hcast (X ||| 1 <<< b)] at h
    have h' : r X + r (X ||| 1 <<< a ||| 1 <<< b) ≤ r (X ||| 1 <<< a) + r (X ||| 1 <<< b) := by
      exact_mod_cast h
    omega
  · -- the basis clauses: `S`, and every window of `σ`
    intro X hX
    simp only [basesCyc, List.mem_cons, List.mem_map, List.mem_range] at hX
    rcases hX with rfl | ⟨i, hi, rfl⟩
    · refine hge4 15 S ?_ hS
      intro s hs
      refine ⟨⟨sEnum.symm ⟨s, hs⟩, by have := (sEnum.symm ⟨s, hs⟩).isLt; omega⟩, ?_, ?_⟩
      · have := (sEnum.symm ⟨s, hs⟩).isLt
        interval_cases h : (sEnum.symm ⟨s, hs⟩ : ℕ) <;> decide
      · rw [hpos, hf_lt _ (sEnum.symm ⟨s, hs⟩).isLt]
        simp
    · refine hge4 _ (cyclicWindow 4 hN σ ⟨i, hi⟩) ?_ (hσ ⟨i, hi⟩)
      rintro x ⟨t, rfl⟩
      refine ⟨⟨4 + (i + t) % N, by have := Nat.mod_lt (i + t) hN0; omega⟩, ?_, ?_⟩
      · exact (testBit_ewin N i _).2 ⟨t, t.isLt, rfl⟩
      · rw [hpos, hf_ge _ (by simp)]
        simp [cyclicIndex]
  · -- no admissible merged sequence works
    intro q hq
    obtain ⟨hlen, hcov, hbound, hfree, -⟩ := hq
    by_contra hall
    push_neg at hall
    have hwin : ∀ j < q.length, 4 ≤ r (window q j) := by
      intro j hj
      have hjs : j ∈ starts true q := by simpa [starts] using hj
      by_cases hS' : hasS q j = true
      · exact hall j (List.mem_filter.2 ⟨hjs, hS'⟩)
      · have hb := hfree j hjs (by simpa using hS')
        simp only [basesCyc, List.mem_cons, List.mem_map, List.mem_range] at hb
        rcases hb with h15 | ⟨i, hi, hwi⟩
        · rw [h15]
          refine hge4 15 S ?_ hS
          intro s hs
          refine ⟨⟨sEnum.symm ⟨s, hs⟩, by have := (sEnum.symm ⟨s, hs⟩).isLt; omega⟩, ?_, ?_⟩
          · have := (sEnum.symm ⟨s, hs⟩).isLt
            interval_cases h : (sEnum.symm ⟨s, hs⟩ : ℕ) <;> decide
          · rw [hpos, hf_lt _ (sEnum.symm ⟨s, hs⟩).isLt]
            simp
        · rw [← hwi]
          refine hge4 _ (cyclicWindow 4 hN σ ⟨i, hi⟩) ?_ (hσ ⟨i, hi⟩)
          rintro x ⟨t, rfl⟩
          refine ⟨⟨4 + (i + t) % N, by have := Nat.mod_lt (i + t) hN0; omega⟩, ?_, ?_⟩
          · exact (testBit_ewin N i _).2 ⟨t, t.isLt, rfl⟩
          · rw [hpos, hf_ge _ (by simp)]
            simp [cyclicIndex]
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
    refine hno ⟨τ, fun j => ?_⟩
    have hsub : maskSet pos (window q j) ⊆ cyclicWindow 4 (by omega) τ j := by
      rintro x ⟨k, hk, rfl⟩
      rw [testBit_window, hlen] at hk
      obtain ⟨t, ht, htk⟩ := hk
      rw [cyclicWindow, Set.mem_range]
      refine ⟨⟨t, ht⟩, ?_⟩
      have hpk : p (cyclicIndex (N + 4) (by omega) j t) = k :=
        Fin.ext (by simpa [p, cyclicIndex] using htk)
      simp [τ, hpk]
    have hWfin : (cyclicWindow 4 (by omega) τ j).Finite := Set.finite_range _
    have h4 : (4 : ℕ∞) ≤ M.eRk (cyclicWindow 4 (by omega) τ j) := by
      have h1 := hwin j (by omega)
      have h2 := M.eRk_mono hsub
      rw [← hcast] at h2
      calc (4 : ℕ∞) ≤ ((r (window q j) : ℕ) : ℕ∞) := by exact_mod_cast h1
        _ ≤ M.eRk (cyclicWindow 4 (by omega) τ j) := h2
    have hWcard : (cyclicWindow 4 (by omega) τ j).encard ≤ 4 := by
      rw [cyclicWindow, ← Set.image_univ]
      exact (Set.encard_image_le _ _).trans (by simp)
    have hind : M.Indep (cyclicWindow 4 (by omega) τ j) :=
      (Matroid.indep_iff_eRk_eq_encard_of_finite (M := M) hWfin).2
        (le_antisymm (M.eRk_le_encard _) (hWcard.trans h4))
    exact hind.isBase_of_eRk_ge hWfin (by rw [hRank]; exact h4)

end Probe.Enc
