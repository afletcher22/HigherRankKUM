import HigherRankKUM.VHT.CoverAveraging

/-!
# Counting heavy flats: a deletable basis for every large uniformly dense matroid

`CoverAveraging.lean` finds a deletable basis among the arcs of a van den Heuvel–Thomassé cover
when the proper heavy flats are few. This file bounds their number by the rank alone.

Let the arcs `W_x` (`x ∈ ZMod p`, weight `q`) be bases of a rank-`r` matroid, and let `F` be a
flat of rank `j` with `(p - q)·j < q·|F|` (*heavy*). The deficiencies `j - |F ∩ W_x|` are
nonnegative and sum to `p·j - q·|F| < q·j`. So all but fewer than `q·j` arcs meet `F` in a basis
of `F` (`card_arc_not_spanning_lt`); call these arcs *good* for `F`.

If `W_x` is good for `F`, then `F = cl(F ∩ W_x)` is determined by the subset `F ∩ W_x` of `W_x`.
So at most `2^r` heavy flats have `W_x` as a good arc. Double counting the good pairs gives

  `#heavy · (p + 1 - q·r) ≤ p · 2^r`    (`card_heavy_mul_le`).

With the cover of weight `r` on `ZMod n`: if `n ≥ r · 2^(r+1)`, there are at most `2^(r+1)` heavy
flats, fewer than `n / (r - 1)`, and the counting theorem applies
(`exists_deletable_basis_of_large`). No strictness is assumed.
-/

namespace HigherRankKUM.VHT

open Set
open scoped Matroid

variable {α : Type*}

/-- The deficiencies of the arcs on a set `F` of rank `j` are nonnegative and sum to
`p·j - q·|F|`. -/
theorem arc_deficiency_sum {M : Matroid α} {p q j : ℕ} [NeZero p] (hqp : q ≤ p)
    (φ : α → ZMod p) (hφ : ∀ x, M.Indep (arcSet M φ (fun _ => q) x))
    {F : Set α} (hFE : F ⊆ M.E) (hFfin : F.Finite) (hFrk : M.eRk F = (j : ℕ∞)) :
    (∀ x, (F ∩ arcSet M φ (fun _ => q) x).ncard ≤ j) ∧
      ∑ x : ZMod p, (j - (F ∩ arcSet M φ (fun _ => q) x).ncard) + F.ncard * q = p * j := by
  let Ff : Finset α := hFfin.toFinset
  have hFfmem : ∀ e, e ∈ Ff ↔ e ∈ F := fun e => hFfin.mem_toFinset
  have hFcard : Ff.card = F.ncard := (Set.ncard_eq_toFinset_card F hFfin).symm
  let A : ZMod p → Finset α := fun x => Ff.filter fun e => (x - φ e).val < q
  have hAeq : ∀ x, ((A x : Finset α) : Set α) = F ∩ arcSet M φ (fun _ => q) x := by
    intro x
    ext e
    constructor
    · intro he
      have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
      have heF : e ∈ F := (hFfmem e).1 he'.1
      exact ⟨heF, hFE heF, he'.2⟩
    · rintro ⟨heF, -, hcond⟩
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨(hFfmem e).2 heF, hcond⟩)
  have hAcard : ∀ x, (F ∩ arcSet M φ (fun _ => q) x).ncard = (A x).card := by
    intro x
    rw [← hAeq x, Set.ncard_coe_finset]
  have hwle : ∀ x, (A x).card ≤ j := by
    intro x
    have hind : M.Indep ((A x : Finset α) : Set α) := by
      rw [hAeq x]
      exact (hφ x).subset Set.inter_subset_right
    have h1 : M.eRk ((A x : Finset α) : Set α) ≤ M.eRk F := by
      apply M.eRk_mono
      rw [hAeq x]
      exact Set.inter_subset_left
    rw [hind.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hFrk] at h1
    exact_mod_cast h1
  have hsum : ∑ x : ZMod p, (A x).card = Ff.card * q := sum_card_arcs Ff φ hqp
  refine ⟨fun x => by rw [hAcard x]; exact hwle x, ?_⟩
  have hδ : ∀ x, (j - (F ∩ arcSet M φ (fun _ => q) x).ncard) + (A x).card = j := by
    intro x
    rw [hAcard x]
    exact Nat.sub_add_cancel (hwle x)
  rw [← hFcard, ← hsum, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun x _ => hδ x),
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]

/-- A heavy set of rank `j` meets all but fewer than `q·j` arcs in `j` elements. -/
theorem card_arc_not_full_lt {M : Matroid α} {p q j : ℕ} [NeZero p] (hqp : q ≤ p)
    (φ : α → ZMod p) (hφ : ∀ x, M.Indep (arcSet M φ (fun _ => q) x))
    {F : Set α} (hFE : F ⊆ M.E) (hFfin : F.Finite) (hFrk : M.eRk F = (j : ℕ∞))
    (hheavy : (p - q) * j < q * F.ncard) (V : Finset (ZMod p))
    (hV : ∀ x ∈ V, (F ∩ arcSet M φ (fun _ => q) x).ncard < j) : V.card < q * j := by
  obtain ⟨-, hsum⟩ := arc_deficiency_sum hqp φ hφ hFE hFfin hFrk
  have h1 : V.card ≤ ∑ x ∈ V, (j - (F ∩ arcSet M φ (fun _ => q) x).ncard) := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun x hx => by
      have := hV x hx
      omega
  have h2 : ∑ x ∈ V, (j - (F ∩ arcSet M φ (fun _ => q) x).ncard) ≤
      ∑ x : ZMod p, (j - (F ∩ arcSet M φ (fun _ => q) x).ncard) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ V)
  have hd : p - q + q = p := Nat.sub_add_cancel hqp
  generalize p - q = d at hheavy hd
  have e : p * j = d * j + q * j := by rw [← hd, Nat.add_mul]
  nlinarith [h1, h2, hsum, hheavy, e]

/-- A heavy flat of rank `j` is spanned by its trace on all but fewer than `q·j` arcs. -/
theorem card_arc_not_spanning_lt {M : Matroid α} {p q j : ℕ} [NeZero p] (hqp : q ≤ p)
    (φ : α → ZMod p) (hφ : ∀ x, M.Indep (arcSet M φ (fun _ => q) x)) (hE : M.E.Finite)
    {F : Set α} (hF : M.IsFlat F) (hFrk : M.eRk F = (j : ℕ∞))
    (hheavy : (p - q) * j < q * F.ncard) (V : Finset (ZMod p))
    (hV : ∀ x ∈ V, M.closure (F ∩ arcSet M φ (fun _ => q) x) ≠ F) : V.card < q * j := by
  have hFE : F ⊆ M.E := hF.subset_ground
  have hFfin : F.Finite := hE.subset hFE
  obtain ⟨hle, -⟩ := arc_deficiency_sum hqp φ hφ hFE hFfin hFrk
  refine card_arc_not_full_lt hqp φ hφ hFE hFfin hFrk hheavy V fun x hx => ?_
  by_contra hnot
  have heq : (F ∩ arcSet M φ (fun _ => q) x).ncard = j := le_antisymm (hle x) (not_lt.mp hnot)
  apply hV x hx
  have hIfin : (F ∩ arcSet M φ (fun _ => q) x).Finite := hFfin.subset Set.inter_subset_left
  have hind : M.Indep (F ∩ arcSet M φ (fun _ => q) x) := (hφ x).subset Set.inter_subset_right
  have hr : M.eRk F ≤ M.eRk (F ∩ arcSet M φ (fun _ => q) x) := by
    rw [hind.eRk_eq_encard, hFrk, ← hIfin.cast_ncard_eq, heq]
  rw [(M.isRkFinite_of_finite hIfin).closure_eq_closure_of_subset_of_eRk_ge_eRk
    Set.inter_subset_left hr]
  exact hF.closure

/-- **Counting heavy flats.** If the arcs of `φ` are bases of a rank-`r` matroid and every member
of `𝓕` is a flat `F` with `(p - q)·r(F) < q·|F|`, then `|𝓕|·(p + 1 - q·r) ≤ p·2^r`. -/
theorem card_heavy_mul_le {M : Matroid α} {p q r : ℕ} [NeZero p] (hqp : q ≤ p)
    (φ : α → ZMod p) (hφ : ∀ x, M.IsBase (arcSet M φ (fun _ => q) x)) (hE : M.E.Finite)
    (hRank : M.eRank = (r : ℕ∞)) (𝓕 : Finset (Set α))
    (h𝓕 : ∀ F ∈ 𝓕, M.IsFlat F ∧ ((p - q : ℕ) : ℕ∞) * M.eRk F < (q : ℕ∞) * F.encard) :
    𝓕.card * (p + 1 - q * r) ≤ p * 2 ^ r := by
  classical
  let Good : Set α → ZMod p → Prop := fun F x =>
    M.closure (F ∩ arcSet M φ (fun _ => q) x) = F
  -- every heavy flat has many good arcs
  have hgood : ∀ F ∈ 𝓕, p + 1 - q * r ≤ (Finset.univ.filter fun x => Good F x).card := by
    intro F hF𝓕
    obtain ⟨hF, hheavy⟩ := h𝓕 F hF𝓕
    have hFfin : F.Finite := hE.subset hF.subset_ground
    have hjle : M.eRk F ≤ (r : ℕ∞) := by
      rw [← hRank]
      exact M.eRk_le_eRank F
    obtain ⟨j, hj, hjr⟩ := ENat.le_natCast_iff.mp hjle
    have hheavy' : (p - q) * j < q * F.ncard := by
      rw [hj, ← hFfin.cast_ncard_eq] at hheavy
      exact_mod_cast hheavy
    have hbad := card_arc_not_spanning_lt hqp φ (fun x => (hφ x).indep) hE hF hj hheavy'
      (Finset.univ.filter fun x => ¬ Good F x) (fun x hx => (Finset.mem_filter.mp hx).2)
    have hcover : (Finset.univ : Finset (ZMod p)) ⊆
        (Finset.univ.filter fun x => Good F x) ∪ (Finset.univ.filter fun x => ¬ Good F x) := by
      intro x _
      by_cases h : Good F x
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)
    have hp : p ≤ (Finset.univ.filter fun x => Good F x).card +
        (Finset.univ.filter fun x => ¬ Good F x).card := by
      have h1 := Finset.card_le_card hcover
      rw [Finset.card_univ, ZMod.card] at h1
      exact h1.trans (Finset.card_union_le _ _)
    have hqj : q * j ≤ q * r := Nat.mul_le_mul_left q hjr
    omega
  -- every arc is good for at most `2^r` heavy flats
  have hper : ∀ x : ZMod p, (𝓕.filter fun F => Good F x).card ≤ 2 ^ r := by
    intro x
    have hWfin : (arcSet M φ (fun _ => q) x).Finite := hE.subset (arcSet_subset M φ _ x)
    let Wf : Finset α := hWfin.toFinset
    have hWcard : Wf.card = r := by
      have h := (hφ x).encard_eq_eRank
      rw [hRank, ← hWfin.cast_ncard_eq, Set.ncard_eq_toFinset_card _ hWfin] at h
      exact_mod_cast h
    have hinj : Set.InjOn (fun F : Set α => Wf.filter fun e => e ∈ F)
        ↑(𝓕.filter fun F => Good F x) := by
      intro F hF F' hF' hEq
      have hF1 : Good F x := (Finset.mem_filter.mp (Finset.mem_coe.mp hF)).2
      have hF2 : Good F' x := (Finset.mem_filter.mp (Finset.mem_coe.mp hF')).2
      have hEq' : (Wf.filter fun e => e ∈ F) = Wf.filter fun e => e ∈ F' := hEq
      have hset : F ∩ arcSet M φ (fun _ => q) x = F' ∩ arcSet M φ (fun _ => q) x := by
        ext e
        constructor
        · rintro ⟨heF, heW⟩
          have hmem : e ∈ Wf.filter fun e => e ∈ F :=
            Finset.mem_filter.mpr ⟨hWfin.mem_toFinset.mpr heW, heF⟩
          rw [hEq'] at hmem
          exact ⟨(Finset.mem_filter.mp hmem).2, heW⟩
        · rintro ⟨heF, heW⟩
          have hmem : e ∈ Wf.filter fun e => e ∈ F' :=
            Finset.mem_filter.mpr ⟨hWfin.mem_toFinset.mpr heW, heF⟩
          rw [← hEq'] at hmem
          exact ⟨(Finset.mem_filter.mp hmem).2, heW⟩
      calc F = M.closure (F ∩ arcSet M φ (fun _ => q) x) := hF1.symm
        _ = M.closure (F' ∩ arcSet M φ (fun _ => q) x) := by rw [hset]
        _ = F' := hF2
    calc (𝓕.filter fun F => Good F x).card ≤ Wf.powerset.card :=
          Finset.card_le_card_of_injOn (fun F : Set α => Wf.filter fun e => e ∈ F)
            (fun F _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _)) hinj
      _ = 2 ^ r := by rw [Finset.card_powerset, hWcard]
  -- double counting of the good pairs
  have hdc : ∑ F ∈ 𝓕, (Finset.univ.filter fun x => Good F x).card =
      ∑ x : ZMod p, (𝓕.filter fun F => Good F x).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  calc 𝓕.card * (p + 1 - q * r) = ∑ _F ∈ 𝓕, (p + 1 - q * r) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ F ∈ 𝓕, (Finset.univ.filter fun x => Good F x).card := Finset.sum_le_sum hgood
    _ = ∑ x : ZMod p, (𝓕.filter fun F => Good F x).card := hdc
    _ ≤ ∑ _x : ZMod p, 2 ^ r := Finset.sum_le_sum fun x _ => hper x
    _ = p * 2 ^ r := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]

theorem le_two_pow (r : ℕ) : r ≤ 2 ^ r := by
  induction r with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hpos : 0 < 2 ^ k := by positivity
    rw [pow_succ]
    omega

theorem two_mul_mul_pred (K r : ℕ) (hr : 0 < r) : 2 * K * (r - 1) + 2 * K = r * (2 * K) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

/-- The arithmetic of the count: for `n ≥ r·2^(r+1)`, a family with
`D·(n + 1 - r²) ≤ n·2^r` has `D·(r - 1) < n`. -/
theorem heavy_count_arith {D n r : ℕ} (hr : 0 < r) (hbig : r * 2 ^ (r + 1) ≤ n)
    (hcount : D * (n + 1 - r * r) ≤ n * 2 ^ r) : D * (r - 1) < n := by
  have hrK : r ≤ 2 ^ r := le_two_pow r
  have hKpos : 0 < 2 ^ r := by positivity
  rw [pow_succ'] at hbig
  generalize 2 ^ r = K at hrK hKpos hbig hcount
  have h2K : 2 * K ≤ r * (2 * K) := Nat.le_mul_of_pos_left (2 * K) hr
  have hn : 0 < n := by omega
  have hrr : 2 * (r * r) ≤ n := by
    calc 2 * (r * r) ≤ 2 * (r * K) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left r hrK)
      _ = r * (2 * K) := by ring
      _ ≤ n := hbig
  have h3 : n ≤ 2 * (n + 1 - r * r) := by omega
  have h6 : n * D ≤ n * (2 * K) := by
    calc n * D = D * n := Nat.mul_comm _ _
      _ ≤ D * (2 * (n + 1 - r * r)) := Nat.mul_le_mul_left _ h3
      _ = 2 * (D * (n + 1 - r * r)) := by ring
      _ ≤ 2 * (n * K) := Nat.mul_le_mul_left 2 hcount
      _ = n * (2 * K) := by ring
  have h7 : D ≤ 2 * K := Nat.le_of_mul_le_mul_left h6 hn
  have h8 : D * (r - 1) ≤ 2 * K * (r - 1) := Nat.mul_le_mul_right _ h7
  have h9 := two_mul_mul_pred K r hr
  omega

/-- **A deletable basis in every large uniformly dense matroid.** A uniformly dense matroid of
rank `r` on `n ≥ r·2^(r+1)` elements has a basis `S` such that `M \ S` is uniformly dense at the
ratio `(n - r) / r`. -/
theorem exists_deletable_basis_of_large (M : Matroid α) {n r : ℕ} (hr : 0 < r)
    (hE : M.E.Finite) (hEcard : M.E.encard = (n : ℕ∞)) (hRank : M.eRank = (r : ℕ∞))
    (hDense : UniformlyDenseRatio M n r) (hbig : r * 2 ^ (r + 1) ≤ n) :
    ∃ S, M.IsBase S ∧ UniformlyDenseRatio (M ↾ (M.E \ S)) (n - r) r := by
  classical
  have hrn : r ≤ n := by
    have h := M.eRk_le_encard M.E
    rw [M.eRk_ground, hRank, hEcard] at h
    exact_mod_cast h
  have hn : 0 < n := by omega
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨φ, hφ⟩ := exists_arc_bases theorem_2_1 M (w := r) (D := n) (n := n) (r := r) hr hrn hE
    hEcard hRank rfl hDense
  let 𝓕 : Finset (Set α) :=
    (hE.toFinset.powerset.image fun s : Finset α => (s : Set α)).filter fun F =>
      M.IsFlat F ∧ F ≠ M.E ∧ ((n - r : ℕ) : ℕ∞) * M.eRk F < (r : ℕ∞) * F.encard
  have hmem : ∀ F, M.IsFlat F → F ≠ M.E →
      ((n - r : ℕ) : ℕ∞) * M.eRk F < (r : ℕ∞) * F.encard → F ∈ 𝓕 := by
    intro F hF hne hheavy
    have hFfin : F.Finite := hE.subset hF.subset_ground
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨hFfin.toFinset, ?_, hFfin.coe_toFinset⟩, hF, hne, hheavy⟩
    exact Finset.mem_powerset.mpr fun e he =>
      hE.mem_toFinset.mpr (hF.subset_ground (hFfin.mem_toFinset.mp he))
  have hcount := card_heavy_mul_le hrn φ hφ hE hRank 𝓕
    (fun F hF => ⟨(Finset.mem_filter.mp hF).2.1, (Finset.mem_filter.mp hF).2.2.2⟩)
  have hD : 𝓕.card * (r - 1) < n := heavy_count_arith hr hbig hcount
  exact exists_deletable_arc M (g := 1) (p := n) (q := r) Nat.one_pos hr hE
    (by rw [Nat.one_mul]; exact hEcard) (by rw [Nat.one_mul]; exact hRank)
    (by rw [Nat.one_mul, Nat.one_mul]; exact hDense) 𝓕 hmem hD

#print axioms exists_deletable_basis_of_large

end HigherRankKUM.VHT
