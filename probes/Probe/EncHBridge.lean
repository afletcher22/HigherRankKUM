import Probe.EncH
import Probe.EncFBridge

/-!
# The hitting lemma on 14 elements, 6-line case: from matroids to `RankModelH`

Let `M` be strict with `t = 0` on 14 elements (`k = 3`), with a 6-element set `L` of rank 2 and
no 9-element plane. Number the ground set with `L` first. If `M` had no deletable basis, the ranks
of the sets named by bitmasks would form a `RankModelH` (`deletable_of_hitLine`):

* every 4-set of rank 4 is a basis. Its complement is not uniformly dense, so it contains a
  3-set of rank at most 1, a 6-set of rank at most 2, or an 8-set of rank at most 3;
* that set is named by `maskOf c` for a sublist `c` of the complementary positions, so `c` is
  one of the listed combinations.
-/

namespace Probe.Enc

open Set HigherRankKUM
open scoped Matroid

variable {α : Type*}

/-! ### Combinations and bitmasks -/

theorem mem_combs : ∀ {n : ℕ} {l c : List ℕ}, c.Sublist l → c.length = n → c ∈ combs n l
  | 0, _, c, _, hlen => by
    rw [List.eq_nil_of_length_eq_zero hlen]
    simp [combs]
  | n + 1, [], c, hs, hlen => by
    rw [List.sublist_nil.1 hs] at hlen
    simp at hlen
  | n + 1, x :: xs, c, hs, hlen => by
    cases hs with
    | cons _ h => exact List.mem_append_right _ (mem_combs h hlen)
    | cons₂ _ h =>
      rw [List.length_cons] at hlen
      exact List.mem_append_left _ (List.mem_map.2 ⟨_, mem_combs h (by omega), rfl⟩)

theorem testBit_maskOf (c : List ℕ) (x : ℕ) : (maskOf c).testBit x = true ↔ x ∈ c := by
  unfold maskOf
  rw [testBit_foldl_or (fun j => j) x c 0]
  simp

theorem pc_maskOf {N : ℕ} {c : List ℕ} (hnd : c.Nodup) (hlt : ∀ x ∈ c, x < N) :
    pc N (maskOf c) = c.length := by
  unfold pc
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, testBit_maskOf, List.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨hlt x h, h⟩⟩

theorem mem_restOf {N B x : ℕ} : x ∈ restOf N B ↔ x < N ∧ B.testBit x = false := by
  simp [restOf]

/-- A set of positions outside `B` is named by one of the combinations of `restOf N B` of its
size. -/
theorem exists_combs_of_subset {M : Matroid α} {N : ℕ} (pos : Fin N ≃ M.E) (B : ℕ) {Z : Set α}
    (hZ : ∀ z ∈ Z, ∃ p : Fin N, (pos p : α) = z ∧ B.testBit p = false) (hZE : Z ⊆ M.E) :
    ∃ c ∈ combs Z.ncard (restOf N B), maskSet pos (maskOf c) = Z := by
  classical
  let c := (restOf N B).filter fun x => decide (∃ h : x < N, (pos ⟨x, h⟩ : α) ∈ Z)
  have hsub : c.Sublist (restOf N B) := List.filter_sublist
  have hnd : c.Nodup := hsub.nodup ((List.nodup_range).filter _)
  have hlt : ∀ x ∈ c, x < N := fun x hx => (mem_restOf.1 (hsub.subset hx)).1
  have hmask : maskSet pos (maskOf c) = Z := by
    apply maskSet_eq pos hZE
    intro p
    rw [testBit_maskOf]
    constructor
    · intro hp
      obtain ⟨-, h⟩ := List.mem_filter.1 hp
      obtain ⟨_, hz⟩ := of_decide_eq_true h
      exact hz
    · intro hz
      obtain ⟨q, hq, hqB⟩ := hZ _ hz
      have hpq : q = p := pos.injective (Subtype.ext hq)
      subst hpq
      exact List.mem_filter.2 ⟨mem_restOf.2 ⟨q.isLt, hqB⟩, decide_eq_true ⟨q.isLt, hz⟩⟩
  have hlen : c.length = Z.ncard := by
    have h := encard_maskSet pos (maskOf c)
    rw [hmask, pc_maskOf hnd hlt] at h
    have hZfin : Z.Finite := Set.finite_of_encard_eq_coe h
    rw [← hZfin.cast_ncard_eq] at h
    exact_mod_cast h.symm
  exact ⟨c, mem_combs hsub hlen, hmask⟩

/-! ### The bridge -/

theorem low14_le {M : Matroid α} (hT : Hitting.StrictT0 M 3) (pos : Fin 14 ≃ M.E)
    (h9 : ∀ F, M.IsFlat F → M.eRk F = 3 → F.encard ≠ ((3 * 3 : ℕ) : ℕ∞)) :
    ∀ X, X < 2 ^ 14 → low14.getD (pc 14 X) 0 ≤ maskRank M pos X := by
  intro X _
  have hYE : maskSet pos X ⊆ M.E := maskSet_subset pos X
  have hYfin : (maskSet pos X).Finite := hT.finite.subset hYE
  have hYcard : (maskSet pos X).ncard = pc 14 X := by
    have h := encard_maskSet pos X
    rw [← hYfin.cast_ncard_eq] at h
    exact_mod_cast h
  obtain ⟨j, hj, hj4⟩ := hT.exists_eRk_eq (maskSet pos X)
  rw [maskRank_eq pos hj, ← hYcard]
  have hpc : (maskSet pos X).ncard ≤ 14 := by
    rw [hYcard]
    unfold pc
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hle : j ≤ 3 → (maskSet pos X).ncard ≤ j * 3 := fun hj3 => hT.ncard_le hYE hj hj3
  have hno9 : j = 3 → (maskSet pos X).ncard ≠ 9 := by
    rintro rfl hY
    obtain ⟨hfl, hrk, hcard⟩ := closure_of_ncard_eq hT hYE hj (by norm_num) (by omega)
    exact h9 _ hfl (by exact_mod_cast hrk) hcard
  have hlow : ∀ s ≤ 14, low14.getD s 0 =
      if s = 0 then 0 else if s ≤ 3 then 1 else if s ≤ 6 then 2 else if s ≤ 8 then 3 else 4 := by
    decide
  rw [hlow _ hpc]
  split_ifs <;> omega

/-- **The hitting lemma on 14 elements with a 6-element rank-2 set and no 9-element plane**,
from its certificate. -/
theorem deletable_of_hitLine
    (hcert : ∀ m : RankModelH 14 low14 (factsOfRanks [(63, 2)]), False)
    {M : Matroid α} (hT : Hitting.StrictT0 M 3) {L : Set α} (hLE : L ⊆ M.E)
    (hLrank : M.eRk L = 2) (hLcard : L.encard = ((6 : ℕ) : ℕ∞))
    (h9 : ∀ F, M.IsFlat F → M.eRk F = 3 → F.encard ≠ ((3 * 3 : ℕ) : ℕ∞)) :
    ∃ S, Hitting.Deletable M 3 S := by
  by_contra hno
  push_neg at hno
  have hEcard : M.E.encard = ((6 + 8 : ℕ) : ℕ∞) := hT.card.trans (by norm_num)
  let aEnum : Fin 6 ≃ L := finEquivOfSetEncard (hT.finite.subset hLE) hLcard
  let bEnum : Fin 8 ≃ (M.E \ L : Set α) :=
    finEquivOfSetEncard (hT.finite.subset diff_subset) (encard_diff_eq hT.finite hLE hEcard hLcard)
  let pos : Fin 14 ≃ M.E := blockEquiv hLE aEnum bEnum
  have hmem : ∀ p : Fin 14, (pos p : α) ∈ L ↔ (p : ℕ) < 6 := blockEquiv_mem_iff hLE aEnum bEnum
  have hL : maskSet pos 63 = L := maskSet_eq pos hLE fun p => by
    rw [hmem p]
    revert p
    decide
  have hranks : ∀ X s, (X, s) ∈ [((63 : ℕ), (2 : ℕ))] → maskRank M pos X = s := by
    intro X s h
    rcases List.mem_singleton.1 h with ⟨⟩
    exact maskRank_eq pos (by rw [hL]; exact_mod_cast hLrank)
  have hRank := hT.rank
  refine hcert
    { r := maskRank M pos
      card := fun X _ => maskRank_card hRank pos X
      low := low14_le hT pos h9
      mono := fun X a _ ha _ => maskRank_mono hRank pos X a ha
      ins := fun X a _ ha _ => maskRank_ins hRank pos X a ha
      sub := fun X a b _ hab hbN ha hb => maskRank_sub hRank pos X a b hab hbN ha hb
      factT := factT_of_ranks hranks
      factF := factF_of_ranks hranks
      noDel := ?_ }
  intro B hB hpc hB4
  -- the 4-set named by `B` is a basis
  set S := maskSet pos B with hSdef
  have hSE : S ⊆ M.E := maskSet_subset pos B
  have hSfin : S.Finite := hT.finite.subset hSE
  have hScard : S.encard = ((4 : ℕ) : ℕ∞) := by rw [hSdef, encard_maskSet, hpc]
  have hSrk : ((4 : ℕ) : ℕ∞) ≤ M.eRk S := by
    rw [← maskRank_cast hRank pos B]
    exact_mod_cast hB4
  have hSind : M.Indep S :=
    (Matroid.indep_iff_eRk_eq_encard_of_finite (M := M) hSfin).2
      (le_antisymm (M.eRk_le_encard _) (hScard.le.trans hSrk))
  have hSbase : M.IsBase S := hSind.isBase_of_eRk_ge hSfin (by rw [hRank]; exact hSrk)
  -- its complement is not uniformly dense
  have hnd := hno S
  simp only [Hitting.Deletable, hSbase, true_and, UniformlyDenseRatio, not_forall] at hnd
  obtain ⟨X, hXsub, hviol⟩ := hnd
  have hXS : X ⊆ M.E \ S := hXsub
  have hXE : X ⊆ M.E := hXS.trans diff_subset
  have hXfin : X.Finite := hT.finite.subset hXE
  rw [Matroid.restrict_eRk_eq M hXS] at hviol
  obtain ⟨j, hj, hj4⟩ := hT.exists_eRk_eq X
  rw [← hXfin.cast_ncard_eq, hj] at hviol
  have hviol' : ¬ 4 * X.ncard ≤ 10 * j := by
    intro h
    apply hviol
    have h' : ((4 * X.ncard : ℕ) : ℕ∞) ≤ ((10 * j : ℕ) : ℕ∞) := by exact_mod_cast h
    simpa using h'
  -- every position of a subset of `X` lies outside `B`
  have hout : ∀ Z ⊆ X, ∀ z ∈ Z, ∃ p : Fin 14, (pos p : α) = z ∧ B.testBit p = false := by
    intro Z hZ z hz
    obtain ⟨p, hp⟩ := pos.surjective ⟨z, hXE (hZ hz)⟩
    have hpz : (pos p : α) = z := by rw [hp]
    refine ⟨p, hpz, ?_⟩
    by_contra hbit
    have hzS : z ∈ S := by
      rw [hSdef, ← hpz]
      exact (mem_maskSet_self pos).2 (by simpa using hbit)
    exact (hXS (hZ hz)).2 hzS
  -- a subset of `X` of size `s`, and its rank
  have hsubset : ∀ n0 : ℕ, n0 ≤ X.ncard →
      ∃ c ∈ combs n0 (restOf 14 B), maskRank M pos (maskOf c) ≤ j := by
    intro n0 hn0
    obtain ⟨Z, hZX, hZcard⟩ := Set.exists_subset_encard_eq
      (show ((n0 : ℕ) : ℕ∞) ≤ X.encard by rw [← hXfin.cast_ncard_eq]; exact_mod_cast hn0)
    have hZfin : Z.Finite := hXfin.subset hZX
    have hZn : Z.ncard = n0 := by
      rw [← hZfin.cast_ncard_eq] at hZcard
      exact_mod_cast hZcard
    obtain ⟨c, hc, hcZ⟩ := exists_combs_of_subset pos B (hout Z hZX) (hZX.trans hXE)
    refine ⟨c, hZn ▸ hc, ?_⟩
    have hle := M.eRk_mono hZX
    rw [← hcZ, ← maskRank_cast hRank pos, hj] at hle
    exact_mod_cast hle
  -- the complement of `S` has 10 elements
  have hdiff : (M.E \ S).ncard = 10 := by
    have h := Set.encard_sdiff_add_encard_of_subset hSE
    rw [hT.card, hScard, ← (hT.finite.subset diff_subset).cast_ncard_eq] at h
    have h' : (M.E \ S).ncard + 4 = 4 * 3 + 2 := by exact_mod_cast h
    omega
  have hXle : X.ncard ≤ 10 := hdiff ▸ Set.ncard_le_ncard hXS (hT.finite.subset diff_subset)
  have hj3 : j ≤ 3 := by
    by_contra h
    have : j = 4 := by omega
    subst this
    omega
  have hX0 : X.ncard ≤ j * 3 := hT.ncard_le hXE hj hj3
  interval_cases j
  · omega
  · obtain ⟨c, hc, hr⟩ := hsubset 3 (by omega)
    exact Or.inl ⟨c, hc, hr⟩
  · obtain ⟨c, hc, hr⟩ := hsubset 6 (by omega)
    exact Or.inr (Or.inl ⟨c, hc, hr⟩)
  · obtain ⟨c, hc, hr⟩ := hsubset 8 (by omega)
    exact Or.inr (Or.inr ⟨c, hc, hr⟩)

end Probe.Enc
