import HigherRankKUM.VHT.Covers
import HigherRankKUM.VHT.Theorem21

/-!
# Block chains

Let `M` be uniformly dense of rank `r = g·q` on `n = g·p` elements, with `gcd(p, q) = 1`, so that
`g = gcd(n, r)` and `p / q` is the density in lowest terms. Van den Heuvel–Thomassé with weight
`q` on `ZMod p` gives `φ : E → ZMod p` whose arcs are bases. The arc at `x` is the union of the
`q` fibres `φ⁻¹(x), φ⁻¹(x - 1), …, φ⁻¹(x - q + 1)`. All arcs have `g·q` elements, so the fibre
sizes are invariant under the shift by `q`, and `gcd(p, q) = 1` makes them all equal to `g`.

So the ground set is a cyclic chain of `p` blocks of `g` elements in which every `q` consecutive
blocks form a basis (`block_chain`).

* `g = 1`: a cyclic basis ordering (coprime KUM).
* `q = 1`: an Edmonds partition into `p` bases.
* `g = 2`, `q = 2`: the pair chains of the rank-4 proof (`Kum10Chain` at `n = 10`).
-/

namespace HigherRankKUM.VHT

open Set

variable {α : Type*}

/-- The fibre of `φ` over `y`: a block of the chain. -/
def fibre (M : Matroid α) {D : ℕ} (φ : α → ZMod D) (y : ZMod D) : Set α :=
  {e | e ∈ M.E ∧ φ e = y}

theorem fibre_subset (M : Matroid α) {D : ℕ} (φ : α → ZMod D) (y : ZMod D) :
    fibre M φ y ⊆ M.E := fun _ h => h.1

/-- For a constant weight `q ≤ D`, the arc at `x` is the union of the fibres over
`x, x - 1, …, x - (q - 1)`. -/
theorem mem_arcSet_const_iff (M : Matroid α) {D q : ℕ} [NeZero D] (hqD : q ≤ D)
    (φ : α → ZMod D) (x : ZMod D) (e : α) :
    e ∈ arcSet M φ (fun _ => q) x ↔ ∃ j < q, e ∈ fibre M φ (x - (j : ZMod D)) := by
  constructor
  · rintro ⟨he, h⟩
    refine ⟨(x - φ e).val, h, he, ?_⟩
    rw [ZMod.natCast_zmod_val]
    ring
  · rintro ⟨j, hj, he, h⟩
    refine ⟨he, ?_⟩
    show (x - φ e).val < q
    rw [h, sub_sub_cancel, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    exact hj

/-- If all the sums of `q` cyclically consecutive values of `F` are equal, then `F` is invariant
under the shift by `q`. -/
theorem window_shift_const {m q c : ℕ} (hq : 0 < q) (F : ZMod m → ℕ)
    (hF : ∀ x : ZMod m, ∑ j ∈ Finset.range q, F (x - j) = c) (x : ZMod m) :
    F x = F (x - q) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
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

/-- If all the sums of `q` cyclically consecutive values of `F` are equal and `gcd(q, m) = 1`,
then `F` is constant. -/
theorem const_of_window_sums {m q c : ℕ} [NeZero m] (hq : 0 < q) (hcop : Nat.Coprime q m)
    (F : ZMod m → ℕ) (hF : ∀ x : ZMod m, ∑ j ∈ Finset.range q, F (x - j) = c) :
    ∀ y, F y = F 0 := by
  have hshift : ∀ (k : ℕ) (x : ZMod m), F x = F (x - k * q) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [ih x, window_shift_const hq F hF (x - k * q)]
      congr 1
      push_cast
      ring
  let u := ZMod.unitOfCoprime q hcop
  have hk : (((u⁻¹ : (ZMod m)ˣ) : ZMod m).val : ZMod m) * q = 1 := by
    rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime q hcop]
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
  exact fun y => by
    have := hconst y.val
    rwa [ZMod.natCast_zmod_val] at this

/-- **Block chains**, given Theorem 2.1. A uniformly dense matroid of rank `g·q` on `g·p`
elements, with `gcd(q, p) = 1`, has a map `φ` to `ZMod p` in which every arc of `q` consecutive
fibres is a basis and every fibre has exactly `g` elements. -/
theorem exists_block_chain (hV : Statement α) (M : Matroid α) {g p q : ℕ} (hg : 0 < g)
    (hq : 0 < q) (hcop : Nat.Coprime q p) (hE : M.E.Finite)
    (hEcard : M.E.encard = ((g * p : ℕ) : ℕ∞)) (hRank : M.eRank = ((g * q : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M (g * p) (g * q)) :
    ∃ φ : α → ZMod p, (∀ x, M.IsBase (arcSet M φ (fun _ => q) x)) ∧
      ∀ y, (fibre M φ y).encard = (g : ℕ∞) := by
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
  refine ⟨φ, hφ, ?_⟩
  classical
  set S := hE.toFinset with hS
  have harc : ∀ x, arcSet M φ (fun _ => q) x = ↑(S.filter fun e => (x - φ e).val < q) := by
    intro x
    ext e
    simp [arcSet, hS]
  have heq : ∀ x, (S.filter fun e => (x - φ e).val < q).card = g * q := by
    intro x
    have h := (hφ x).encard_eq_eRank
    rw [hRank, harc x, Set.encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  let F : ZMod p → ℕ := fun y => (S.filter fun e => φ e = y).card
  have hF : ∀ x : ZMod p, ∑ j ∈ Finset.range q, F (x - j) = g * q := by
    intro x
    have h := card_arc_filter hqp S φ x
    rw [heq x] at h
    exact h.symm
  have hall := const_of_window_sums hq hcop F hF
  have h0 : F 0 = g := by
    have hs : ∑ j ∈ Finset.range q, F ((0 : ZMod p) - j) = q * F 0 := by
      rw [Finset.sum_congr rfl (fun (j : ℕ) _ => hall ((0 : ZMod p) - (j : ZMod p))),
        Finset.sum_const,
        Finset.card_range, smul_eq_mul]
    have h := hF 0
    rw [hs] at h
    exact Nat.eq_of_mul_eq_mul_left hq (h.trans (Nat.mul_comm g q))
  intro y
  have hset : fibre M φ y = ↑(S.filter fun e => φ e = y) := by
    ext e
    simp [fibre, hS]
  have hFy : (S.filter fun e => φ e = y).card = g := (hall y).trans h0
  rw [hset, Set.encard_coe_eq_coe_finsetCard, hFy]

/-- **Block chains.** A uniformly dense matroid of rank `g·q` on `g·p` elements, with
`gcd(q, p) = 1`, is a cyclic chain of `p` blocks of `g` elements in which every `q` consecutive
blocks form a basis. -/
theorem block_chain (M : Matroid α) {g p q : ℕ} (hg : 0 < g) (hq : 0 < q)
    (hcop : Nat.Coprime q p) (hE : M.E.Finite)
    (hEcard : M.E.encard = ((g * p : ℕ) : ℕ∞)) (hRank : M.eRank = ((g * q : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M (g * p) (g * q)) :
    ∃ φ : α → ZMod p, (∀ x, M.IsBase (arcSet M φ (fun _ => q) x)) ∧
      ∀ y, (fibre M φ y).encard = (g : ℕ∞) :=
  exists_block_chain theorem_2_1 M hg hq hcop hE hEcard hRank hDense

#print axioms block_chain

end HigherRankKUM.VHT
