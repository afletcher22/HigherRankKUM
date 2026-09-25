import Probe.EncSound
import HigherRankKUM.FullSolver
import HigherRankKUM.CyclicOrder

/-!
# Palomar probe: from matroids to rank models (round 3)

A uniformly dense rank-4 matroid on `N` elements with no cyclic basis ordering yields a
`RankModel N`: number the ground set by `σ : Fin N ≃ M.E`, read a bitmask `X` as the set
`maskSet σ X`, and take `r X` to be its rank.  Combined with a kernel-checked refutation, this
proves KUM at that size.
-/

namespace Probe.Enc

open Set HigherRankKUM

variable {α : Type*}

/-! ### Bitmasks -/

theorem testBit_or_shift (X a j : ℕ) :
    (X ||| 1 <<< a).testBit j = true ↔ X.testBit j = true ∨ a = j := by
  simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq]

theorem testBit_foldl_or (f : ℕ → ℕ) (x : ℕ) : ∀ (L : List ℕ) (acc : ℕ),
    (L.foldl (fun acc j => acc ||| 1 <<< f j) acc).testBit x = true ↔
      acc.testBit x = true ∨ ∃ t ∈ L, f t = x
  | [], acc => by simp
  | t :: L, acc => by
    simp only [List.foldl_cons, testBit_foldl_or f x L, testBit_or_shift, List.mem_cons,
      exists_eq_or_imp]
    tauto

theorem testBit_window (s : List ℕ) (i x : ℕ) :
    (window s i).testBit x = true ↔ ∃ t < 4, s.getD ((i + t) % s.length) 0 = x :=
  (testBit_foldl_or (fun j => s.getD ((i + j) % s.length) 0) x (List.range 4) 0).trans
    (by simp [List.mem_range])

/-! ### The set named by a bitmask -/

/-- The elements named by the bitmask `X`, through a numbering `σ` of the ground set. -/
def maskSet {N : ℕ} {E : Set α} (σ : Fin N ≃ E) (X : ℕ) : Set α :=
  {x | ∃ j : Fin N, X.testBit j = true ∧ (σ j : α) = x}

theorem maskSet_subset {N : ℕ} {E : Set α} (σ : Fin N ≃ E) (X : ℕ) : maskSet σ X ⊆ E := by
  rintro _ ⟨j, -, rfl⟩
  exact (σ j).2

theorem mem_maskSet_self {N : ℕ} {E : Set α} (σ : Fin N ≃ E) {X : ℕ} {j : Fin N} :
    (σ j : α) ∈ maskSet σ X ↔ X.testBit j = true := by
  constructor
  · rintro ⟨j', hj', h⟩
    have : j' = j := σ.injective (Subtype.ext h)
    subst this
    exact hj'
  · intro h
    exact ⟨j, h, rfl⟩

theorem maskSet_insert {N : ℕ} {E : Set α} (σ : Fin N ≃ E) (X a : ℕ) (ha : a < N) :
    maskSet σ (X ||| 1 <<< a) = insert (σ ⟨a, ha⟩ : α) (maskSet σ X) := by
  ext x
  simp only [maskSet, mem_setOf_eq, mem_insert_iff, testBit_or_shift]
  constructor
  · rintro ⟨j, hj | hj, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩
    · left
      have : (⟨a, ha⟩ : Fin N) = j := Fin.ext hj
      rw [this]
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨⟨a, ha⟩, Or.inr rfl, rfl⟩
    · exact ⟨j, Or.inl hj, rfl⟩

theorem encard_maskSet {N : ℕ} {E : Set α} (σ : Fin N ≃ E) (X : ℕ) :
    (maskSet σ X).encard = pc N X := by
  have h1 : maskSet σ X = (fun j : Fin N => (σ j : α)) '' {j | X.testBit j = true} := by
    ext x
    simp only [maskSet, mem_setOf_eq, mem_image]
  have h2 : (Fin.val '' {j : Fin N | X.testBit j = true}) =
      ↑((Finset.range N).filter fun m => X.testBit m = true) := by
    ext m
    simp only [mem_image, mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, h⟩
      subst h
      exact ⟨j.2, hj⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨m, h1⟩, h2, rfl⟩
  have hinj : Function.Injective (fun j : Fin N => (σ j : α)) :=
    fun a b h => σ.injective (Subtype.ext h)
  rw [h1, hinj.encard_image, ← Fin.val_injective.encard_image {j : Fin N | X.testBit j = true},
    h2, Set.encard_coe_eq_coe_finsetCard]
  rfl

/-! ### The bridge -/

/-- A numbering of a finite ground set of known size. -/
noncomputable def finEquivGround {M : Matroid α} {N : ℕ} (hE : M.E.Finite)
    (hEcard : M.E.encard = ((N : ℕ) : ℕ∞)) : Fin N ≃ M.E := by
  haveI : Finite M.E := hE.to_subtype
  have hn : M.E.ncard = N := by
    have hcast : (M.E.ncard : ℕ∞) = (N : ℕ∞) := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast
  have hNat : Nat.card M.E = N := by
    simpa only [Nat.card_coe_set_eq] using hn
  exact (Finite.equivFinOfCardEq hNat).symm

/-- A uniformly dense rank-4 matroid on `N` elements with no cyclic basis ordering gives a rank
model on `N` bits. -/
theorem rankModel_of_no_cbo {M : Matroid α} {N : ℕ} (hN : 0 < N) (hE : M.E.Finite)
    (hRank : M.eRank = ((4 : ℕ) : ℕ∞)) (hEcard : M.E.encard = ((N : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M N 4)
    (hno : ¬ ∃ τ : Fin N ≃ M.E, CyclicBasisOrder M 4 hN τ) : Nonempty (RankModel N) := by
  let σ : Fin N ≃ M.E := finEquivGround hE hEcard
  let r : ℕ → ℕ := fun X => (M.eRk (maskSet σ X)).toNat
  have hcast : ∀ X, ((r X : ℕ) : ℕ∞) = M.eRk (maskSet σ X) := fun X =>
    ENat.coe_toNat (ne_top_of_le_ne_top (by rw [hRank]; exact ENat.coe_ne_top 4)
      (M.eRk_le_eRank _))
  refine ⟨{ r := r, card := ?_, dens := ?_, mono := ?_, ins := ?_, sub := ?_, noCBO := ?_ }⟩
  · intro X _
    have h := M.eRk_le_encard (maskSet σ X)
    rw [← hcast X, encard_maskSet] at h
    exact_mod_cast h
  · intro X _
    have h := hDense (maskSet σ X) (maskSet_subset σ X)
    rw [encard_maskSet, ← hcast X] at h
    exact_mod_cast h
  · intro X a _ ha _
    have h := M.eRk_mono (show maskSet σ X ⊆ maskSet σ (X ||| 1 <<< a) by
      rw [maskSet_insert σ X a ha]
      exact subset_insert _ _)
    rw [← hcast X, ← hcast (X ||| 1 <<< a)] at h
    exact_mod_cast h
  · intro X a _ ha _
    have h := M.eRk_insert_le_add_one (σ ⟨a, ha⟩ : α) (maskSet σ X)
    rw [← maskSet_insert σ X a ha, ← hcast X, ← hcast (X ||| 1 <<< a)] at h
    exact_mod_cast h
  · intro X a b _ hab hbN ha hb
    have haN : a < N := by omega
    have hA := maskSet_insert σ X a haN
    have hB := maskSet_insert σ X b hbN
    have hAB := maskSet_insert σ (X ||| 1 <<< a) b hbN
    have hna : (σ ⟨a, haN⟩ : α) ∉ maskSet σ X := by
      rw [mem_maskSet_self]
      simpa using ha
    have hnb : (σ ⟨b, hbN⟩ : α) ∉ maskSet σ X := by
      rw [mem_maskSet_self]
      simpa using hb
    have hne : (σ ⟨a, haN⟩ : α) ≠ (σ ⟨b, hbN⟩ : α) := by
      intro h
      have h' := σ.injective (Subtype.ext h)
      simp only [Fin.mk.injEq] at h'
      omega
    have hU : maskSet σ (X ||| 1 <<< a ||| 1 <<< b) =
        maskSet σ (X ||| 1 <<< a) ∪ maskSet σ (X ||| 1 <<< b) := by
      rw [hAB, hA, hB]
      ext x
      simp only [mem_insert_iff, mem_union]
      tauto
    have hI : maskSet σ (X ||| 1 <<< a) ∩ maskSet σ (X ||| 1 <<< b) = maskSet σ X := by
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
    have h := M.eRk_inter_add_eRk_union_le (maskSet σ (X ||| 1 <<< a))
      (maskSet σ (X ||| 1 <<< b))
    rw [hI, ← hU, ← hcast X, ← hcast (X ||| 1 <<< a ||| 1 <<< b), ← hcast (X ||| 1 <<< a),
      ← hcast (X ||| 1 <<< b)] at h
    have h' : r X + r (X ||| 1 <<< a ||| 1 <<< b) ≤ r (X ||| 1 <<< a) + r (X ||| 1 <<< b) := by
      exact_mod_cast h
    omega
  · intro s hlen hcov hbound
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
    let τ : Fin N ≃ M.E := (Equiv.ofBijective p hbij).trans σ
    refine hno ⟨τ, fun i => ?_⟩
    have hsub : maskSet σ (window s i) ⊆ cyclicWindow 4 hN τ i := by
      rintro x ⟨j, hj, rfl⟩
      rw [testBit_window, hlen] at hj
      obtain ⟨t, ht, htj⟩ := hj
      rw [cyclicWindow, Set.mem_range]
      refine ⟨⟨t, ht⟩, ?_⟩
      have hpj : p (cyclicIndex N hN i t) = j := Fin.ext (by simpa [p, cyclicIndex] using htj)
      simp [τ, hpj]
    have hWfin : (cyclicWindow 4 hN τ i).Finite := Set.finite_range _
    have h4 : (4 : ℕ∞) ≤ M.eRk (cyclicWindow 4 hN τ i) := by
      have h1 := hall i i.2
      have h2 := M.eRk_mono hsub
      rw [← hcast] at h2
      calc (4 : ℕ∞) ≤ ((r (window s i) : ℕ) : ℕ∞) := by exact_mod_cast h1
        _ ≤ M.eRk (cyclicWindow 4 hN τ i) := h2
    have hWcard : (cyclicWindow 4 hN τ i).encard ≤ 4 := by
      rw [cyclicWindow, ← Set.image_univ]
      exact (Set.encard_image_le _ _).trans (by simp)
    have hind : M.Indep (cyclicWindow 4 hN τ i) :=
      (Matroid.indep_iff_eRk_eq_encard_of_finite (M := M) hWfin).2
        (le_antisymm (M.eRk_le_encard _) (hWcard.trans h4))
    exact hind.isBase_of_eRk_ge hWfin (by rw [hRank]; exact_mod_cast h4)

end Probe.Enc
