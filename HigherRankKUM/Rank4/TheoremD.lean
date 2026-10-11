import HigherRankKUM.VHT.Theorem21
import HigherRankKUM.VHT.Covers

/-!
# Theorem D: rank-4 KUM on `4k` elements

Let `M` be a uniformly dense rank-4 matroid on `4k` elements.

* `k = 1`: the ground set is a basis, so any ordering works.
* `k = 2`: the 8-element case, taken here as an explicit input.
* `k ≥ 3`: van den Heuvel–Thomassé splits `E` into `k` bases, the fibres of one mapping.
  Deleting one basis leaves a uniformly dense matroid on `4(k - 1)` elements, which is ordered by
  induction. The rank-4 extension theorem, taken here as an explicit input, then inserts the
  deleted basis.

Both inputs are finite statements: SAT-certified in the research ledger (`RANK4_EXTENSION_THEOREM.md`
§§2–3), or, for `k = 2`, a consequence of Kotlar–Ziv.
-/

namespace HigherRankKUM

open Set
open scoped Matroid

variable {α : Type*}

/-- **The rank-4 extension theorem on `N` elements.** If `S` is a basis of a rank-4 matroid and
the other `N` elements have a cyclic ordering whose 4-windows are bases, then the whole matroid
has a cyclic basis ordering. -/
def Rank4Extension (α : Type*) (N : ℕ) : Prop :=
  ∀ (M : Matroid α) (S : Set α) (hN : 0 < N), M.E.Finite → M.eRank = 4 → M.IsBase S →
    (∃ σ : Fin N ≃ (M.E \ S : Set α), CyclicBasisOrder M 4 hN σ) →
    ∃ τ : Fin (N + 4) ≃ M.E, CyclicBasisOrder M 4 (by omega) τ

/-- A numbering of a finite ground set of known size. -/
noncomputable def finEquivOfEncard {M : Matroid α} {n : ℕ} (hE : M.E.Finite)
    (h : M.E.encard = (n : ℕ∞)) : Fin n ≃ M.E := by
  haveI : Finite M.E := hE.to_subtype
  have hn : M.E.ncard = n := by
    have hcast : (M.E.ncard : ℕ∞) = n := by
      rw [hE.cast_ncard_eq]
      exact h
    exact_mod_cast hcast
  exact (Finite.equivFinOfCardEq (by simpa only [Nat.card_coe_set_eq] using hn)).symm

/-- A window of length `r ≤ n` has exactly `r` elements. -/
theorem encard_cyclicWindow {E : Set α} {n r : ℕ} (hn : 0 < n) (hrn : r ≤ n) (σ : Fin n ≃ E)
    (i : Fin n) : (cyclicWindow r hn σ i).encard = r := by
  rw [cyclicWindow, Function.Injective.encard_range]
  · simp
  · intro a b h
    have ha := a.2
    have hb := b.2
    have h2 := σ.injective (Subtype.ext h)
    exact Fin.ext (cyclicIndex_injective_offsets n hn i (by omega) (by omega) h2)

/-- A basis of a restriction of full rank is a basis of the matroid. -/
theorem isBase_of_isBase_restrict {M : Matroid α} {R B : Set α} (hR : R ⊆ M.E)
    (hB : (M ↾ R).IsBase B) (hrk : M.eRk R = M.eRank) (hfin : B.Finite) : M.IsBase B := by
  have hBR := (Matroid.isBase_restrict_iff hR).1 hB
  exact hBR.indep.isBase_of_eRk_ge hfin (by rw [hBR.eRk_eq_eRk, hrk])

/-- Deleting one of `k` disjoint bases that cover `E` (the fibres of `φ`) leaves a matroid that is
uniformly dense at `k - 1`. -/
theorem uniformlyDense_restrict_of_fibres {M : Matroid α} {k : ℕ} [NeZero k] (hE : M.E.Finite)
    {φ : α → ZMod k} (hφ : ∀ x, M.Indep {e | e ∈ M.E ∧ φ e = x}) {X : Set α}
    (hX : X ⊆ M.E \ {e | e ∈ M.E ∧ φ e = 0}) (hrfin : M.eRk X ≠ ⊤) :
    X.encard ≤ ((k - 1 : ℕ) : ℕ∞) * M.eRk X := by
  classical
  have hXfin : X.Finite := hE.subset (hX.trans diff_subset)
  set T := hXfin.toFinset with hT
  set r := (M.eRk X).toNat with hr
  have hrc : (r : ℕ∞) = M.eRk X := ENat.coe_toNat hrfin
  have hfib : ∀ x, (T.filter fun e => φ e = x).card ≤ r := by
    intro x
    have hsub : (↑(T.filter fun e => φ e = x) : Set α) ⊆ {e | e ∈ M.E ∧ φ e = x} := by
      intro e he
      simp only [Finset.coe_filter, mem_setOf_eq, hT, Set.Finite.mem_toFinset] at he
      exact ⟨(hX he.1).1, he.2⟩
    have hind := (hφ x).subset hsub
    have h1 := hind.eRk_eq_encard
    have h2 := M.eRk_mono (show (↑(T.filter fun e => φ e = x) : Set α) ⊆ X by
      intro e he
      simp only [Finset.coe_filter, mem_setOf_eq, hT, Set.Finite.mem_toFinset] at he
      exact he.1)
    rw [h1, Set.encard_coe_eq_coe_finsetCard, ← hrc] at h2
    exact_mod_cast h2
  have hzero : (T.filter fun e => φ e = 0).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hφe
    simp only [hT, Set.Finite.mem_toFinset] at he
    exact (hX he).2 ⟨(hX he).1, hφe⟩
  have hsum := Finset.card_eq_sum_card_fiberwise (f := φ) (s := T) (t := Finset.univ)
    (fun e _ => Finset.mem_univ (φ e))
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod k)), hzero, add_zero] at hsum
  have hle : T.card ≤ (k - 1) * r := by
    rw [hsum]
    calc ∑ x ∈ Finset.univ.erase (0 : ZMod k), (T.filter fun e => φ e = x).card
        ≤ ∑ _x ∈ Finset.univ.erase (0 : ZMod k), r := Finset.sum_le_sum fun x _ => hfib x
      _ = (k - 1) * r := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          ZMod.card, smul_eq_mul]
  have hXT : X.encard = T.card := by
    rw [hT, ← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset]
  rw [hXT, ← hrc]
  exact_mod_cast hle

/-- **Theorem D.** Given the rank-4 extension theorem on `4k` elements (`k ≥ 2`) and KUM on 8
elements, rank-4 KUM holds on `4k` elements. -/
theorem solvesDivisibleKUMAtRank_four (hext : ∀ k, 2 ≤ k → Rank4Extension α (4 * k))
    (h8 : SolvesKUMAtRankSize α 4 8) : SolvesDivisibleKUMAtRank α 4 := by
  intro M k hr hk hE hRank hEcard hDense
  induction k using Nat.strong_induction_on generalizing M with
  | h k ih =>
  have hRank4 : M.eRank = 4 := by simpa using hRank
  rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | hk3
  · -- `k = 1`: every window is the whole ground set, which is a basis
    let σ := finEquivOfEncard hE hEcard
    refine ⟨σ, fun i => ?_⟩
    have hsub : cyclicWindow 4 (Nat.mul_pos hr hk) σ i ⊆ M.E := by
      rintro _ ⟨j, rfl⟩
      exact (σ _).2
    have hEeq : cyclicWindow 4 (Nat.mul_pos hr hk) σ i = M.E :=
      hE.eq_of_subset_of_encard_le' hsub (by
        rw [encard_cyclicWindow _ (by norm_num) σ i, hEcard])
    rw [hEeq]
    have hind : M.Indep M.E := by
      rw [Matroid.indep_iff_eRk_eq_encard_of_finite hE, M.eRk_ground, hRank4, hEcard]
      norm_num
    exact hind.isBase_of_eRk_ge hE (by rw [M.eRk_ground])
  · -- `k = 2`: the 8-element input
    have hDense8 : UniformlyDenseRatio M 8 4 := by
      intro X hX
      have h := hDense X hX
      calc ((4 : ℕ) : ℕ∞) * X.encard ≤ ((4 : ℕ) : ℕ∞) * (((2 : ℕ) : ℕ∞) * M.eRk X) := by gcongr
        _ = ((8 : ℕ) : ℕ∞) * M.eRk X := by push_cast; ring
    obtain ⟨order, horder⟩ := h8 M hr (by norm_num) hE hRank (by rw [hEcard]) hDense8
    exact exists_cyclicBasisOrder_congr M (by norm_num) rfl ⟨order, horder⟩
  · -- `k ≥ 3`: delete one basis of an Edmonds partition, order the rest, and extend
    haveI : NeZero k := ⟨by omega⟩
    obtain ⟨φ, hφ⟩ := VHT.exists_arc_bases VHT.theorem_2_1 M (w := 1) (D := k) (n := 4 * k)
      (r := 4) Nat.one_pos (by omega) hE hEcard hRank (by ring)
      ((uniformlyDenseRatio_one_iff M k).2 hDense)
    have hfib : ∀ x, VHT.arcSet M φ (fun _ => 1) x = {e | e ∈ M.E ∧ φ e = x} := by
      intro x
      ext e
      simp only [VHT.arcSet, mem_setOf_eq, Nat.lt_one_iff, ZMod.val_eq_zero, sub_eq_zero]
      exact and_congr_right fun _ => eq_comm
    set S := {e | e ∈ M.E ∧ φ e = 0} with hS
    have hSbase : M.IsBase S := by
      rw [hS, ← hfib 0]
      exact hφ 0
    have hSE : S ⊆ M.E := hSbase.subset_ground
    set R := M.E \ S with hR
    have hRE : R ⊆ M.E := diff_subset
    have hbase1 : M.IsBase {e | e ∈ M.E ∧ φ e = 1} := by
      rw [← hfib 1]
      exact hφ 1
    have h1R : {e | e ∈ M.E ∧ φ e = 1} ⊆ R := by
      rintro e ⟨he, h1⟩
      refine ⟨he, fun hS' => ?_⟩
      have h0 : φ e = 0 := hS'.2
      rw [h0] at h1
      haveI : Fact (1 < k) := ⟨by omega⟩
      exact zero_ne_one h1
    have hrkR : M.eRk R = M.eRank := by
      refine le_antisymm (M.eRk_le_eRank R) ?_
      rw [← hbase1.encard_eq_eRank, ← hbase1.indep.eRk_eq_encard]
      exact M.eRk_mono h1R
    have hrfin : ∀ X, M.eRk X ≠ ⊤ := fun X =>
      ne_top_of_le_ne_top (by rw [hRank]; exact ENat.coe_ne_top 4) (M.eRk_le_eRank X)
    -- the smaller instance
    have hE' : (M ↾ R).E.Finite := hE.subset hRE
    have hRank' : (M ↾ R).eRank = ((4 : ℕ) : ℕ∞) := by
      rw [← Matroid.eRk_ground, Matroid.restrict_ground_eq, Matroid.restrict_eRk_eq _ subset_rfl,
        hrkR, hRank]
    have hEcard' : (M ↾ R).E.encard = ((4 * (k - 1) : ℕ) : ℕ∞) := by
      rw [Matroid.restrict_ground_eq]
      have h : R.encard + S.encard = M.E.encard := Set.encard_sdiff_add_encard_of_subset hSE
      rw [hEcard, hSbase.encard_eq_eRank, hRank] at h
      have hfinR : R.encard ≠ ⊤ := (hE.subset hRE).encard_lt_top.ne
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfinR
      rw [← hm] at h ⊢
      have h' : m + 4 = 4 * k := by exact_mod_cast h
      congr 1
      omega
    have hDense' : UniformlyDense (M ↾ R) (k - 1) := by
      intro X hX
      have hXR : X ⊆ R := hX
      rw [Matroid.restrict_eRk_eq M hXR]
      refine uniformlyDense_restrict_of_fibres hE (fun x => ?_) hXR (hrfin X)
      rw [← hfib x]
      exact (hφ x).indep
    obtain ⟨σ', hσ'⟩ := ih (k - 1) (by omega) (M ↾ R) (by omega) hE' hRank' hEcard' hDense'
    -- its windows are bases of `M`
    have hcbo : CyclicBasisOrder M 4 (Nat.mul_pos hr (show 0 < k - 1 by omega)) σ' := by
      intro i
      refine isBase_of_isBase_restrict hRE (hσ' i) hrkR ?_
      exact Set.finite_range _
    obtain ⟨τ, hτ⟩ := hext (k - 1) (by omega) M S (Nat.mul_pos hr (by omega)) hE hRank4
      hSbase ⟨σ', hcbo⟩
    exact exists_cyclicBasisOrder_congr M (by omega) rfl ⟨τ, hτ⟩

end HigherRankKUM
