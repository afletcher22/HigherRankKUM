import Probe.VHT.Core
import HigherRankKUM.TightContraction

/-!
# Theorem 2.1 of van den Heuvel–Thomassé: the proof

Strong induction on the size of the ground set.

* An element of weight `0` covers no point, so remove it by restriction.
* An element of weight `D` covers every point. Condition (b) forces it to be a nonloop and gives
  every other element weight at least `1`. So condition (b) passes to the contraction, which stays
  loopless, and the element is added back to every point set.
* Otherwise every weight lies between `1` and `D - 1`, which is the core case (`core`).
-/

namespace HigherRankKUM.VHT

open Set
open scoped Matroid

variable {α : Type*}

theorem loopless_restrict {N : Matroid α} (hL : N.Loopless) {R : Set α} (hR : R ⊆ N.E) :
    (N ↾ R).Loopless := by
  rw [Matroid.loopless_iff_forall_not_isLoop]
  intro e heR hloop
  rw [Matroid.restrict_isLoop_iff] at hloop
  rcases hloop.2 with h | h
  · exact (Matroid.loopless_iff_forall_not_isLoop.1 hL) e (hR heR) h
  · exact h (hR heR)

theorem weightBounded_restrict {N : Matroid α} {ω : α → ℕ} {D : ℕ} (hW : WeightBounded N ω D)
    {R : Set α} (hR : R ⊆ N.E) : WeightBounded (N ↾ R) ω D := by
  intro A hA
  have hAR : (A : Set α) ⊆ R := hA
  rw [Matroid.restrict_eRk_eq N hAR]
  exact hW A (hAR.trans hR)

/-- **van den Heuvel–Thomassé, Theorem 2.1**, direction (b) ⇒ (a). -/
theorem statement : Statement α := by
  classical
  intro M ω D hD hE hL hW
  haveI : NeZero D := ⟨hD.ne'⟩
  suffices h : ∀ n : ℕ, ∀ N : Matroid α, N.E.ncard = n → N.E.Finite → N.Loopless →
      WeightBounded N ω D → ∃ φ : α → ZMod D, ∀ x, N.Indep (arcSet N φ ω x) from
    h _ M rfl hE hL hW
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih N hn hNE hNL hNW
  have ih' : ∀ N' : Matroid α, N'.E ⊂ N.E → N'.Loopless → WeightBounded N' ω D →
      ∃ φ : α → ZMod D, ∀ x, N'.Indep (arcSet N' φ ω x) := fun N' hss hL' hW' =>
    ih _ (hn ▸ Set.ncard_lt_ncard hss hNE) N' rfl (hNE.subset hss.subset) hL' hW'
  by_cases h0 : ∃ e ∈ N.E, ω e = 0
  · obtain ⟨e, he, hωe⟩ := h0
    have hss : N.E \ {e} ⊂ N.E := Set.diff_singleton_ssubset.2 he
    obtain ⟨φ, hφ⟩ := ih' (N ↾ (N.E \ {e})) hss (loopless_restrict hNL diff_subset)
      (weightBounded_restrict hNW diff_subset)
    refine ⟨φ, fun x => ?_⟩
    have heq : arcSet N φ ω x = arcSet (N ↾ (N.E \ {e})) φ ω x := by
      ext a
      simp only [arcSet, mem_setOf_eq, Matroid.restrict_ground_eq, mem_diff, mem_singleton_iff]
      constructor
      · rintro ⟨ha, hx⟩
        refine ⟨⟨ha, ?_⟩, hx⟩
        rintro rfl
        omega
      · rintro ⟨⟨ha, -⟩, hx⟩
        exact ⟨ha, hx⟩
    rw [heq]
    exact (hφ x).of_restrict
  push_neg at h0
  by_cases hDe : ∃ e ∈ N.E, D ≤ ω e
  · obtain ⟨e, he, hDωe⟩ := hDe
    have hne : N.IsNonloop e := (Matroid.loopless_iff_forall_isNonloop.1 hNL) e he
    have hωeD : ω e = D := by
      have h := hNW {e} (by simpa using he)
      rw [Finset.sum_singleton, Finset.coe_singleton, hne.eRk_eq, mul_one] at h
      have : ω e ≤ D := by exact_mod_cast h
      omega
    have hL' : (N ／ {e}).Loopless := by
      rw [Matroid.loopless_iff_forall_not_isLoop]
      intro f hf hloop
      rw [Matroid.contract_isLoop_iff_mem_closure] at hloop
      have hfE : f ∈ N.E := hf.1
      have hfe : f ≠ e := fun h => hf.2 (by simp [h])
      have hsub : ({e, f} : Set α) ⊆ N.closure {e} := by
        rintro a (rfl | ha)
        · exact N.mem_closure_of_mem (mem_singleton a) (by simpa using he)
        · rw [mem_singleton_iff] at ha
          rw [ha]
          exact hloop.1
      have hrk : N.eRk ({e, f} : Set α) ≤ 1 := by
        calc N.eRk ({e, f} : Set α) ≤ N.eRk (N.closure {e}) := N.eRk_mono hsub
          _ = N.eRk {e} := N.eRk_closure_eq _
          _ = 1 := hne.eRk_eq
      have hcoe : ((({e, f} : Finset α)) : Set α) ⊆ N.E := by
        rw [Finset.coe_pair]
        exact insert_subset he (singleton_subset_iff.2 hfE)
      have h := hNW {e, f} hcoe
      rw [Finset.sum_pair hfe.symm, Finset.coe_pair] at h
      have h' : ((ω e + ω f : ℕ) : ℕ∞) ≤ (D : ℕ∞) :=
        (h.trans (mul_le_mul_left' hrk _)).trans_eq (mul_one _)
      have h'' : ω e + ω f ≤ D := by exact_mod_cast h'
      have := h0 f hfE
      omega
    have hW' : WeightBounded (N ／ {e}) ω D := by
      intro A hA
      have heA : e ∉ A := fun h => (hA (Finset.mem_coe.2 h)).2 rfl
      have hAE : ((insert e A : Finset α) : Set α) ⊆ N.E := by
        rw [Finset.coe_insert]
        exact insert_subset he (hA.trans diff_subset)
      have h := hNW (insert e A) hAE
      rw [Finset.sum_insert heA, Finset.coe_insert, hωeD] at h
      have hrk := eRk_union_eq_contract_eRk_add N (X := {e}) (A := (A : Set α))
        (by simpa using he) hA
      rw [hne.eRk_eq, union_singleton] at hrk
      rw [hrk] at h
      have hfin : (N ／ {e}).eRk (A : Set α) ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp) ((N ／ {e}).eRk_le_encard _)
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hfin
      rw [← hk] at h ⊢
      have h2 : D + A.sum ω ≤ D * (k + 1) := by exact_mod_cast h
      have h3 : A.sum ω ≤ D * k := by nlinarith
      exact_mod_cast h3
    obtain ⟨φ, hφ⟩ := ih' (N ／ {e})
      (by rw [Matroid.contract_ground]; exact Set.diff_singleton_ssubset.2 he) hL' hW'
    refine ⟨φ, fun x => ?_⟩
    have heq : arcSet N φ ω x = insert e (arcSet (N ／ {e}) φ ω x) := by
      ext a
      simp only [arcSet, mem_setOf_eq, mem_insert_iff, Matroid.contract_ground, mem_diff,
        mem_singleton_iff]
      constructor
      · rintro ⟨ha, hx⟩
        by_cases hae : a = e
        · exact Or.inl hae
        · exact Or.inr ⟨⟨ha, hae⟩, hx⟩
      · rintro (rfl | ⟨⟨ha, -⟩, hx⟩)
        · refine ⟨he, ?_⟩
          rw [hωeD]
          exact ZMod.val_lt _
        · exact ⟨ha, hx⟩
    rw [heq]
    have h := hφ x
    rw [hne.contractElem_indep_iff] at h
    exact h.2
  push_neg at hDe
  exact core hNE hNL hNW (fun e he => Nat.one_le_iff_ne_zero.2 (h0 e he)) hDe ih'

/-- **Coprime KUM**, unconditionally: van den Heuvel–Thomassé, Theorem 3.1. -/
theorem coprime_kum' {r m : ℕ} (hcop : Nat.Coprime r m) : SolvesKUMAtRankSize α r m :=
  coprime_kum statement hcop

#print axioms statement
#print axioms coprime_kum'

end HigherRankKUM.VHT
