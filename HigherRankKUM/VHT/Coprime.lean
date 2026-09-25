import HigherRankKUM.VHT.Statement
import HigherRankKUM.FullSolver
import HigherRankKUM.CyclicOrder

/-!
# Coprime KUM from Theorem 2.1 (van den Heuvel–Thomassé, Theorem 3.1)

Give every element weight `r = r(M)` and take `D = m = |E|`. Theorem 2.1 gives `φ : E → ZMod m` in
which every set of elements covering a point is independent. The argument then runs:

1. Double counting shows each such set has exactly `r` elements.
2. So the fibre sizes of `φ` have all their length-`r` window sums equal to `r`.
3. Since `gcd(r, m) = 1`, every fibre has size `1`, and `φ` is a bijection.
4. The length-`r` windows of its inverse are arcs of `φ`, so they are independent sets of size
   `r`, that is, bases.
-/

namespace HigherRankKUM.VHT

open Set

variable {α : Type*}

/-! ### Window sums on `ZMod m` -/

/-- If every `r` cyclically consecutive values of `F` ending at any point sum to `r`, then `F`
is invariant under the shift by `r`. -/
theorem window_shift {m r : ℕ} (hr : 0 < r) (F : ZMod m → ℕ)
    (hF : ∀ x : ZMod m, ∑ j ∈ Finset.range r, F (x - j) = r) (x : ZMod m) :
    F x = F (x - r) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have h1 := hF x
  have h2 := hF (x - 1)
  rw [Finset.sum_range_succ'] at h1
  rw [Finset.sum_range_succ] at h2
  have h3 : ∑ j ∈ Finset.range n, F (x - ((j + 1 : ℕ) : ZMod m)) =
      ∑ j ∈ Finset.range n, F (x - 1 - (j : ZMod m)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast
    ring
  have h4 : x - 1 - ((n : ℕ) : ZMod m) = x - ((n + 1 : ℕ) : ZMod m) := by
    push_cast
    ring
  rw [h3] at h1
  rw [h4] at h2
  simp only [Nat.cast_zero, sub_zero] at h1
  omega

/-- If every `r` consecutive values of `F` sum to `r`, `gcd(r, m) = 1`, and all values sum to
`m`, then `F ≡ 1`. -/
theorem eq_one_of_window_sums {m r : ℕ} [NeZero m] (hr : 0 < r) (hcop : Nat.Coprime r m)
    (F : ZMod m → ℕ) (hF : ∀ x : ZMod m, ∑ j ∈ Finset.range r, F (x - j) = r)
    (hsum : ∑ y, F y = m) : ∀ y, F y = 1 := by
  have hshift : ∀ (k : ℕ) (x : ZMod m), F x = F (x - k * r) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [ih x, window_shift hr F hF (x - k * r)]
      congr 1
      push_cast
      ring
  let u := ZMod.unitOfCoprime r hcop
  have hk : (((u⁻¹ : (ZMod m)ˣ) : ZMod m).val : ZMod m) * r = 1 := by
    rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime r hcop]
    exact u.inv_mul
  have hstep : ∀ x : ZMod m, F x = F (x - 1) := by
    intro x
    have := hshift (((u⁻¹ : (ZMod m)ˣ) : ZMod m).val) x
    rwa [hk] at this
  have hconst : ∀ n : ℕ, F (n : ZMod m) = F 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hstep, ← ih]
      congr 1
      push_cast
      ring
  have hall : ∀ y, F y = F 0 := fun y => by
    have := hconst y.val
    rwa [ZMod.natCast_zmod_val] at this
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have h0 : F 0 = 1 := by
    have hs : ∑ y : ZMod m, F y = m * F 0 := by
      rw [Finset.sum_congr rfl (fun y _ => hall y), Finset.sum_const, Finset.card_univ,
        ZMod.card, smul_eq_mul]
    rw [hs] at hsum
    exact Nat.eq_of_mul_eq_mul_left hm (hsum.trans (mul_one m).symm)
  exact fun y => (hall y).trans h0

/-! ### Arcs and fibres -/

/-- Each point is covered by exactly `r` elements in total, summed over the points. -/
theorem sum_card_arcs {m : ℕ} [NeZero m] (S : Finset α) (φ : α → ZMod m) {r : ℕ}
    (hrm : r ≤ m) :
    ∑ x : ZMod m, (S.filter fun e => (x - φ e).val < r).card = S.card * r := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have h : ∀ e ∈ S, (∑ x : ZMod m, if (x - φ e).val < r then 1 else 0) = r := by
    intro e _
    rw [← Finset.card_filter, card_arc, min_eq_left hrm]
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul]

/-- The elements covering `x` are the fibres of `φ` over the `r` points ending at `x`. -/
theorem card_arc_filter [DecidableEq α] {m r : ℕ} [NeZero m] (hrm : r ≤ m) (S : Finset α)
    (φ : α → ZMod m)
    (x : ZMod m) :
    (S.filter fun e => (x - φ e).val < r).card =
      ∑ j ∈ Finset.range r, (S.filter fun e => φ e = x - j).card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨he, h⟩
      refine ⟨(x - φ e).val, h, he, ?_⟩
      rw [ZMod.natCast_zmod_val]
      ring
    · rintro ⟨j, hj, he, h⟩
      refine ⟨he, ?_⟩
      rw [h, sub_sub_cancel, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      exact hj
  · intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    rw [Function.onFun, Finset.disjoint_left]
    intro e he hek
    simp only [Finset.mem_filter] at he hek
    apply hjk
    have h : ((j : ℕ) : ZMod m) = k := sub_right_injective (he.2.symm.trans hek.2)
    have h' := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h'

/-! ### Theorem 3.1 -/

/-- **van den Heuvel–Thomassé, Theorem 3.1.** Given Theorem 2.1, KUM holds whenever the rank
and the ground-set size are coprime. -/
theorem coprime_kum (hV : Statement α) {r m : ℕ} (hcop : Nat.Coprime r m) :
    SolvesKUMAtRankSize α r m := by
  intro M hr hm hE hRank hEcard hDense
  haveI : NeZero m := ⟨hm.ne'⟩
  classical
  set S := hE.toFinset with hS
  have hScard : S.card = m := by
    have h : ((S.card : ℕ) : ℕ∞) = m := by
      rw [hS, ← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset]
      exact hEcard
    exact_mod_cast h
  have hrm : r ≤ m := by
    have h := M.eRk_le_encard M.E
    rw [M.eRk_ground, hRank, hEcard] at h
    exact_mod_cast h
  have hLoop : M.Loopless := by
    rw [Matroid.loopless_iff_forall_not_isLoop]
    intro e heE heLoop
    have h := hDense {e} (by simpa using heE)
    rw [Set.encard_singleton, heLoop.eRk_eq] at h
    simp at h
    omega
  have hWB : WeightBounded M (fun _ => r) m := by
    intro A hA
    have h := hDense (A : Set α) hA
    rw [Set.encard_coe_eq_coe_finsetCard] at h
    simp only [Finset.sum_const, smul_eq_mul]
    push_cast
    exact le_of_eq_of_le (mul_comm _ _) h
  obtain ⟨φ, hφ⟩ := hV M (fun _ => r) m hm hE hLoop hWB
  have harc : ∀ x, arcSet M φ (fun _ => r) x = ↑(S.filter fun e => (x - φ e).val < r) := by
    intro x
    ext e
    simp [arcSet, hS]
  have hle : ∀ x, (S.filter fun e => (x - φ e).val < r).card ≤ r := by
    intro x
    have h1 := (hφ x).eRk_eq_encard
    have h2 := M.eRk_le_eRank (arcSet M φ (fun _ => r) x)
    rw [h1, hRank, harc x, Set.encard_coe_eq_coe_finsetCard] at h2
    exact_mod_cast h2
  have heq : ∀ x, (S.filter fun e => (x - φ e).val < r).card = r := by
    have hsumr : ∑ x : ZMod m, (S.filter fun e => (x - φ e).val < r).card =
        ∑ _x : ZMod m, r := by
      rw [sum_card_arcs S φ hrm, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul,
        hScard]
    intro x
    exact (Finset.sum_eq_sum_iff_of_le (fun x _ => hle x)).1 hsumr x (Finset.mem_univ x)
  let F : ZMod m → ℕ := fun y => (S.filter fun e => φ e = y).card
  have hF : ∀ x : ZMod m, ∑ j ∈ Finset.range r, F (x - j) = r := by
    intro x
    have h := card_arc_filter hrm S φ x
    rw [heq x] at h
    exact h.symm
  have hsumF : ∑ y, F y = m := by
    have h := Finset.card_eq_sum_card_fiberwise (f := φ) (s := S) (t := Finset.univ)
      (fun e _ => Finset.mem_univ (φ e))
    rw [hScard] at h
    exact h.symm
  have hF1 := eq_one_of_window_sums hr hcop F hF hsumF
  have hinj : Function.Injective (fun e : M.E => φ e) := by
    intro a b hab
    have hab' : φ a = φ b := hab
    have ha : (a : α) ∈ S.filter fun e => φ e = φ a := by simp [hS, a.2]
    have hb : (b : α) ∈ S.filter fun e => φ e = φ a := by simp [hS, b.2, hab']
    exact Subtype.ext (Finset.card_le_one.1 (hF1 (φ a)).le _ ha _ hb)
  have hsurj : Function.Surjective (fun e : M.E => φ e) := by
    intro y
    have hcard : (S.filter fun e => φ e = y).card = 1 := hF1 y
    obtain ⟨e, he⟩ := Finset.card_pos.1 (by omega : 0 < (S.filter fun e => φ e = y).card)
    simp only [Finset.mem_filter, hS, Set.Finite.mem_toFinset] at he
    exact ⟨⟨e, he.1⟩, he.2⟩
  let ι : Fin m ≃ ZMod m := Equiv.ofBijective (fun i : Fin m => ((i : ℕ) : ZMod m))
    ⟨fun i j h => Fin.ext (by
        have h' := congrArg ZMod.val h
        simpa [ZMod.val_natCast, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] using h'),
     fun y => ⟨⟨y.val, ZMod.val_lt y⟩, ZMod.natCast_zmod_val y⟩⟩
  let τ0 : M.E ≃ ZMod m := Equiv.ofBijective _ ⟨hinj, hsurj⟩
  let σ : Fin m ≃ M.E := ι.trans τ0.symm
  have hσ : ∀ i : Fin m, φ (σ i : α) = ((i : ℕ) : ZMod m) := by
    intro i
    show (fun e : M.E => φ e) (τ0.symm (ι i)) = ι i
    exact τ0.apply_symm_apply (ι i)
  refine ⟨σ, fun i => ?_⟩
  let x : ZMod m := ((i.val + (r - 1) : ℕ) : ZMod m)
  have hsub : cyclicWindow r hm σ i ⊆ arcSet M φ (fun _ => r) x := by
    intro e he
    rw [cyclicWindow, Set.mem_range] at he
    obtain ⟨j, rfl⟩ := he
    refine ⟨(σ _).2, ?_⟩
    show (x - φ (σ (cyclicIndex m hm i j.val) : α)).val < r
    have hj := j.2
    rw [hσ]
    have hci : ((cyclicIndex m hm i j.val : Fin m) : ℕ) = (i.val + j.val) % m := rfl
    rw [hci, ZMod.natCast_mod, ← Nat.cast_sub (by omega), ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hWind : M.Indep (cyclicWindow r hm σ i) := (hφ x).subset hsub
  have hWfin : (cyclicWindow r hm σ i).Finite := Set.finite_range _
  have hWcard : (cyclicWindow r hm σ i).encard = r := by
    rw [cyclicWindow, Function.Injective.encard_range]
    · simp
    · intro a b h
      have ha := a.2
      have hb := b.2
      have h2 := σ.injective (Subtype.ext h)
      exact Fin.ext (cyclicIndex_injective_offsets m hm i (by omega) (by omega) h2)
  exact hWind.isBase_of_eRk_ge hWfin (by rw [hRank, hWind.eRk_eq_encard, hWcard])

end HigherRankKUM.VHT
