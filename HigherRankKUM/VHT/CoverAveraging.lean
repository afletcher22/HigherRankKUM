import HigherRankKUM.VHT.Covers
import HigherRankKUM.VHT.Theorem21
import Mathlib.Combinatorics.Pigeonhole

/-!
# Averaging over a van den Heuvel–Thomassé cover: deletable bases

Let `M` be uniformly dense of rank `g·q` on `g·p` elements. Van den Heuvel–Thomassé with weight
`q` on `ZMod p` gives `p` bases (the arcs), with every element in exactly `q` of them.

A basis `S` is *deletable* if `M \ S` is uniformly dense at the ratio `(p - q) / q`. An arc `W`
fails to be deletable exactly when some `X` disjoint from `W` has `q·|X| > (p - q)·r(X)`. Then
the flat `F = cl(X)` is *violated* by `W`: `q·|F \ W| > (p - q)·r(F)`.

**Averaging** (`card_arc_violations_lt`). Fix `F` of rank `j` and put `δ_x = j - |F ∩ W_x| ≥ 0`.
Every element of `F` lies in `q` arcs, so `Σ_x δ_x = p·j - q·|F|`. The arc `W_x` violates `F`
exactly when `q·δ_x > Σ_y δ_y`. So fewer than `q` arcs violate `F`.

**Counting** (`exists_deletable_arc`). A violated flat is proper and *heavy*:
`q·|F| > (p - q)·r(F)`. If the proper heavy flats number fewer than `p / (q - 1)`, some arc violates none of them and is deletable.
For `q = 1` (the divisible case) every arc is deletable; this is the deletion step of Theorem D.
For `q = 2` every heavy flat rules out at most one arc; this is the mechanism of Lemma U.
-/

namespace HigherRankKUM.VHT

open Set
open scoped Matroid

variable {α : Type*}

/-- If each `x ∈ V` has `q · δ x` larger than the total of `δ`, then `V` has fewer than `q`
elements. -/
theorem card_lt_of_sum_lt {ι : Type*} (s V : Finset ι) (δ : ι → ℕ) {q : ℕ} (hq : 0 < q)
    (hVs : V ⊆ s) (hV : ∀ x ∈ V, ∑ y ∈ s, δ y < q * δ x) : V.card < q := by
  by_contra hlt
  have hqV : q ≤ V.card := not_lt.mp hlt
  have h1 : V.card * (∑ y ∈ s, δ y + 1) ≤ ∑ x ∈ V, q * δ x := by
    have h0 : ∑ _x ∈ V, (∑ y ∈ s, δ y + 1) = V.card * (∑ y ∈ s, δ y + 1) := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [← h0]
    exact Finset.sum_le_sum fun x hx => Nat.succ_le_of_lt (hV x hx)
  have h2 : ∑ x ∈ V, q * δ x ≤ q * ∑ y ∈ s, δ y := by
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left q (Finset.sum_le_sum_of_subset hVs)
  have h3 : q * (∑ y ∈ s, δ y + 1) ≤ V.card * (∑ y ∈ s, δ y + 1) :=
    Nat.mul_le_mul_right _ hqV
  have h5 := Nat.le_of_mul_le_mul_left (h3.trans (h1.trans h2)) hq
  omega

/-- The arithmetic of one violation. With `T = Σ δ = p·j - q·f`, `d = j - w` and a set of `xc`
elements of `F` outside the arc, `(p - q)·j < q·xc` gives `T < q·d`. -/
theorem violation_arith {p q j f w xc T d : ℕ} (hqp : q ≤ p) (hT : T + f * q = p * j)
    (hd : d + w = j) (hsplit : xc + w ≤ f) (hviol : (p - q) * j < q * xc) : T < q * d := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hqp
  rw [Nat.add_sub_cancel_left] at hviol
  have e1 : q * (xc + w) ≤ q * f := Nat.mul_le_mul_left q hsplit
  have e2 : q * (d + w) = q * j := by rw [hd]
  nlinarith [e1, e2, hT, hviol]

/-- **Averaging.** Let the arcs of `φ` with constant weight `q` be independent, and let `F` have
rank `j`. Then fewer than `q` arcs `W` admit a set `X ⊆ F` disjoint from `W` with
`(p - q)·j < q·|X|`. -/
theorem card_arc_violations_lt {M : Matroid α} {p q j : ℕ} [NeZero p] (hq : 0 < q)
    (hqp : q ≤ p) (φ : α → ZMod p) (hφ : ∀ x, M.Indep (arcSet M φ (fun _ => q) x))
    {F : Set α} (hFE : F ⊆ M.E) (hFfin : F.Finite) (hFrk : M.eRk F = (j : ℕ∞))
    (V : Finset (ZMod p))
    (hV : ∀ x ∈ V, ∃ X : Set α, X ⊆ F ∧ Disjoint X (arcSet M φ (fun _ => q) x) ∧
      (p - q) * j < q * X.ncard) :
    V.card < q := by
  let Ff : Finset α := hFfin.toFinset
  have hFfmem : ∀ e, e ∈ Ff ↔ e ∈ F := fun e => hFfin.mem_toFinset
  have hFcard : Ff.card = F.ncard := (Set.ncard_eq_toFinset_card F hFfin).symm
  let A : ZMod p → Finset α := fun x => Ff.filter fun e => (x - φ e).val < q
  have hAF : ∀ x, ((A x : Finset α) : Set α) ⊆ F := by
    intro x e he
    exact (hFfmem e).1 (Finset.mem_filter.mp (Finset.mem_coe.mp he)).1
  have hAarc : ∀ x, ((A x : Finset α) : Set α) ⊆ arcSet M φ (fun _ => q) x := by
    intro x e he
    have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    exact ⟨hFE ((hFfmem e).1 he'.1), he'.2⟩
  have hwle : ∀ x, (A x).card ≤ j := by
    intro x
    have hind : M.Indep ((A x : Finset α) : Set α) := (hφ x).subset (hAarc x)
    have h1 := M.eRk_mono (hAF x)
    rw [hind.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hFrk] at h1
    exact_mod_cast h1
  have hsum : ∑ x : ZMod p, (A x).card = Ff.card * q := sum_card_arcs Ff φ hqp
  let δ : ZMod p → ℕ := fun x => j - (A x).card
  have hδ : ∀ x, δ x + (A x).card = j := fun x => Nat.sub_add_cancel (hwle x)
  have hT : ∑ x : ZMod p, δ x + Ff.card * q = p * j := by
    rw [← hsum, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun x _ => hδ x),
      Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  refine card_lt_of_sum_lt Finset.univ V δ hq (Finset.subset_univ V) ?_
  intro x hx
  obtain ⟨X, hXF, hXdisj, hviol⟩ := hV x hx
  have hXfin : X.Finite := hFfin.subset hXF
  have hsplit : X.ncard + (A x).card ≤ Ff.card := by
    have hdisj : Disjoint X ((A x : Finset α) : Set α) := hXdisj.mono_right (hAarc x)
    have hU := Set.ncard_union_eq hdisj hXfin (Finset.finite_toSet (A x))
    have hle := Set.ncard_le_ncard (Set.union_subset hXF (hAF x)) hFfin
    rw [hU, Set.ncard_coe_finset] at hle
    rw [hFcard]
    exact hle
  exact violation_arith hqp hT (hδ x) hsplit hviol

/-- **A deletable basis by counting heavy flats**, given Theorem 2.1. Let `M` be uniformly dense
of rank `g·q` on `g·p` elements, and let `𝓕` contain every proper flat `F` with
`(p - q)·r(F) < q·|F|`. If `|𝓕|·(q - 1) < p`, some basis `S` has `M \ S` uniformly dense at the
ratio `(p - q) / q`. -/
theorem exists_deletable_arc_of_statement (hV : Statement α) (M : Matroid α) {g p q : ℕ}
    (hg : 0 < g) (hq : 0 < q) (hE : M.E.Finite)
    (hEcard : M.E.encard = ((g * p : ℕ) : ℕ∞)) (hRank : M.eRank = ((g * q : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M (g * p) (g * q))
    (𝓕 : Finset (Set α))
    (h𝓕 : ∀ F, M.IsFlat F → F ≠ M.E →
      ((p - q : ℕ) : ℕ∞) * M.eRk F < (q : ℕ∞) * F.encard → F ∈ 𝓕)
    (hcount : 𝓕.card * (q - 1) < p) :
    ∃ S, M.IsBase S ∧ UniformlyDenseRatio (M ↾ (M.E \ S)) (p - q) q := by
  have hqp : q ≤ p := by
    have h := M.eRk_le_encard M.E
    rw [M.eRk_ground, hRank, hEcard] at h
    have h' : g * q ≤ g * p := by exact_mod_cast h
    exact Nat.le_of_mul_le_mul_left h' hg
  have hp : 0 < p := by omega
  haveI : NeZero p := ⟨hp.ne'⟩
  have hDense' : UniformlyDenseRatio M p q := UniformlyDenseRatio.unscale M p q g hg hDense
  obtain ⟨φ, hφ⟩ := exists_arc_bases hV M (w := q) (D := p) (n := g * p) (r := g * q) hq hqp hE
    hEcard hRank (by ring) hDense'
  by_contra hno
  -- every arc fails to be deletable: choose a witness
  have hbad : ∀ x : ZMod p, ∃ X : Set α, X ⊆ M.E ∧ Disjoint X (arcSet M φ (fun _ => q) x) ∧
      ((p - q : ℕ) : ℕ∞) * M.eRk X < (q : ℕ∞) * X.encard := by
    intro x
    by_contra hx
    refine hno ⟨arcSet M φ (fun _ => q) x, hφ x, fun X hX => ?_⟩
    have hXR : X ⊆ M.E \ arcSet M φ (fun _ => q) x := hX
    rw [Matroid.restrict_eRk_eq M hXR]
    by_contra hlt
    exact hx ⟨X, hXR.trans Set.sdiff_subset,
      Set.disjoint_left.2 fun e heX heA => (hXR heX).2 heA, not_le.mp hlt⟩
  choose X hXE hXdisj hXviol using hbad
  -- the closure of each witness is a heavy flat
  have hheavy : ∀ x, M.closure (X x) ∈ 𝓕 := by
    intro x
    have hne : M.closure (X x) ≠ M.E := by
      -- a witness of full rank would have more than `|E| - r(M)` elements outside a basis
      intro hcl
      have hXfin : (X x).Finite := hE.subset (hXE x)
      have hr : M.eRk (X x) = ((g * q : ℕ) : ℕ∞) := by
        rw [← M.eRk_closure_eq, hcl, M.eRk_ground, hRank]
      have hWcard : (arcSet M φ (fun _ => q) x).encard = ((g * q : ℕ) : ℕ∞) := by
        rw [(hφ x).encard_eq_eRank, hRank]
      have hU : (X x ∪ arcSet M φ (fun _ => q) x).encard ≤ M.E.encard :=
        Set.encard_mono (Set.union_subset (hXE x) (arcSet_subset M φ _ x))
      rw [Set.encard_union_eq (hXdisj x), hWcard, hEcard, ← hXfin.cast_ncard_eq] at hU
      have hU' : (X x).ncard + g * q ≤ g * p := by exact_mod_cast hU
      have hv := hXviol x
      rw [hr, ← hXfin.cast_ncard_eq] at hv
      have hv' : (p - q) * (g * q) < q * (X x).ncard := by exact_mod_cast hv
      obtain ⟨d, hdq⟩ : ∃ d, d = p - q := ⟨_, rfl⟩
      rw [← hdq] at hv'
      have hd : d + q = p := by omega
      have h1 : q * ((X x).ncard + g * q) ≤ q * (g * p) := Nat.mul_le_mul_left q hU'
      have e2 : q * (g * p) = q * (g * d) + q * (g * q) := by
        rw [← hd]
        ring
      nlinarith [h1, e2, hv']
    refine h𝓕 _ (M.isFlat_closure (X x)) hne ?_
    rw [M.eRk_closure_eq]
    have hsub : X x ⊆ M.closure (X x) := M.subset_closure (X x) (hXE x)
    have hmono : (X x).encard ≤ (M.closure (X x)).encard := Set.encard_mono hsub
    calc ((p - q : ℕ) : ℕ∞) * M.eRk (X x) < (q : ℕ∞) * (X x).encard := hXviol x
      _ ≤ (q : ℕ∞) * (M.closure (X x)).encard := by gcongr
  -- pigeonhole: some heavy flat is the closure of at least `q` witnesses
  classical
  obtain ⟨F, -, hFcard⟩ : ∃ F ∈ 𝓕,
      q - 1 < (Finset.univ.filter fun x : ZMod p => M.closure (X x) = F).card :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := (Finset.univ : Finset (ZMod p))) (t := 𝓕) (f := fun x => M.closure (X x))
      (n := q - 1) (fun x _ => hheavy x) (by rw [Finset.card_univ, ZMod.card]; exact hcount)
  have hpos : 0 < (Finset.univ.filter fun x : ZMod p => M.closure (X x) = F).card := by omega
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hpos
  have hx0F : M.closure (X x0) = F := (Finset.mem_filter.mp hx0).2
  have hFE : F ⊆ M.E := hx0F ▸ M.closure_subset_ground (X x0)
  have hFfin : F.Finite := hE.subset hFE
  have hFrkle : M.eRk F ≤ ((g * q : ℕ) : ℕ∞) := by
    rw [← hRank]
    exact M.eRk_le_eRank F
  obtain ⟨j, hj, -⟩ := ENat.le_natCast_iff.mp hFrkle
  have hlt := card_arc_violations_lt hq hqp φ (fun x => (hφ x).indep) hFE hFfin hj
    (Finset.univ.filter fun x : ZMod p => M.closure (X x) = F) (by
      intro x hx
      have hxF : M.closure (X x) = F := (Finset.mem_filter.mp hx).2
      have hXF : X x ⊆ F := hxF ▸ M.subset_closure (X x) (hXE x)
      have hXfin : (X x).Finite := hFfin.subset hXF
      have hr : M.eRk (X x) = (j : ℕ∞) := by rw [← M.eRk_closure_eq, hxF, hj]
      have h := hXviol x
      rw [hr, ← hXfin.cast_ncard_eq] at h
      exact ⟨X x, hXF, hXdisj x, by exact_mod_cast h⟩)
  omega

/-- **A deletable basis by counting heavy flats.** Let `M` be uniformly dense of rank `g·q` on
`g·p` elements, and let `𝓕` contain every proper flat `F` with `(p - q)·r(F) < q·|F|`. If
`|𝓕|·(q - 1) < p`, some basis `S` has `M \ S` uniformly dense at the ratio `(p - q) / q`. -/
theorem exists_deletable_arc (M : Matroid α) {g p q : ℕ}
    (hg : 0 < g) (hq : 0 < q) (hE : M.E.Finite)
    (hEcard : M.E.encard = ((g * p : ℕ) : ℕ∞)) (hRank : M.eRank = ((g * q : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M (g * p) (g * q))
    (𝓕 : Finset (Set α))
    (h𝓕 : ∀ F, M.IsFlat F → F ≠ M.E →
      ((p - q : ℕ) : ℕ∞) * M.eRk F < (q : ℕ∞) * F.encard → F ∈ 𝓕)
    (hcount : 𝓕.card * (q - 1) < p) :
    ∃ S, M.IsBase S ∧ UniformlyDenseRatio (M ↾ (M.E \ S)) (p - q) q :=
  exists_deletable_arc_of_statement theorem_2_1 M hg hq hE hEcard hRank hDense 𝓕 h𝓕 hcount

#print axioms exists_deletable_arc

end HigherRankKUM.VHT
