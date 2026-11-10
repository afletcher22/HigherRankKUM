import HigherRankKUM.Skeleton

/-!
# Induction on the multiple at a fixed density

Write the size and the rank as `n = p·g` and `r = q·g` with `gcd(p, q) = 1`, so that `p / q` is
the density in lowest terms and `g = gcd(n, r)`.

A nonempty proper tight set `X` has rank `q·a` with `0 < a < g`
(`exists_tight_rank_factorization`). Its restriction and contraction are uniformly dense at the
same ratio `p / q`, of sizes `p·a` and `p·(g - a)`. So KUM at the multiple `g` follows from KUM
at the smaller multiples of the same ratio, and only the strict case is left at each multiple:

* `solvesKUMAtRankSize_mul_of_strict`: KUM at `(q·g, p·g)` from the strict cases at
  `(q·g', p·g')` for `2 ≤ g' ≤ g`. The multiple `1` is coprime KUM.

For `g = 2` both factors have the multiple `1`, so the tight case needs no hypothesis:

* `exists_cyclicBasisOrder_of_two_mul_of_nonempty_proper_tight`: every uniformly dense matroid
  with `gcd(n, r) = 2` and a nonempty proper tight set has a cyclic basis ordering, in every rank.
* `solvesKUMAtRankSize_two_mul_of_strict`: KUM at `(2q, 2p)` from its strict case.

Unlike the rank-`r` skeleton, this uses no solver at another density.
-/

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/-- **Induction on the multiple at a fixed density `p / q`.** KUM at rank `q·g` and size `p·g`
follows from the strict cases at the multiples `2 ≤ g' ≤ g`. -/
theorem solvesKUMAtRankSize_mul_of_strict {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p.Coprime q) (g : ℕ)
    (hStrict : ∀ g', 2 ≤ g' → g' ≤ g → SolvesStrictKUMAtRankSize α (q * g') (p * g')) :
    SolvesKUMAtRankSize α (q * g) (p * g) := by
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro N hr hn hE hRank hEcard hDense
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · rw [h, Nat.mul_zero] at hr
      omega
    · exact h
  by_cases hg1 : g = 1
  · -- the multiple `1` is the coprime case
    subst hg1
    have hcop : Nat.Coprime (q * 1) (p * 1) := by
      rw [Nat.mul_one, Nat.mul_one]
      exact hpq.symm
    exact VHT.solvesKUMAtRankSize_of_coprime hcop N hr hn hE hRank hEcard hDense
  have hDense' : UniformlyDenseRatio N p q := by
    apply UniformlyDenseRatio.unscale N p q g hg
    rw [Nat.mul_comm g p, Nat.mul_comm g q]
    exact hDense
  by_cases htight : ∃ X, TightRatio N (p * g) (q * g) X ∧ X.Nonempty ∧ X ≠ N.E
  · -- a tight set: glue the two factors, which have smaller multiples
    obtain ⟨X, hX, hne, hprop⟩ := htight
    have hX' : TightRatio N p q X := by
      apply TightRatio.unscale N p q g hg
      rw [Nat.mul_comm g p, Nat.mul_comm g q]
      exact hX
    obtain ⟨a, b, ha, hb, hab, hXrank⟩ :=
      exists_tight_rank_factorization N hp hq hg hpq hE hRank hEcard hX' hne hprop
    have hSolveA : SolvesKUMAtRankSize α (a * q) (a * p) := by
      rw [Nat.mul_comm a q, Nat.mul_comm a p]
      exact ih a (by omega) (fun g' h2 hle => hStrict g' h2 (by omega))
    have hSolveB : SolvesKUMAtRankSize α (b * q) (b * p) := by
      rw [Nat.mul_comm b q, Nat.mul_comm b p]
      exact ih b (by omega) (fun g' h2 hle => hStrict g' h2 (by omega))
    have hOrder :=
      exists_cyclicBasisOrder_of_ratio_tight_of_rank_solutions
        (M := N) (X := X) (a := a) (b := b) (p := p) (q := q)
        ha hb hp hq hE
        (by simpa [hab, Nat.mul_comm] using hEcard)
        (by simpa [hab, Nat.mul_comm] using hRank)
        hDense' hX' hXrank hSolveA hSolveB
    subst hab
    exact exists_cyclicBasisOrder_congr N
      (Nat.mul_comm (a + b) p) (Nat.mul_comm (a + b) q) hOrder
  · -- no tight set: the strict case
    have hS : StrictlyUniformlyDenseRatio N (p * g) (q * g) := fun X hX hne hprop =>
      lt_of_le_of_ne (hDense X hX) fun heq => htight ⟨X, ⟨hX, heq⟩, hne, hprop⟩
    exact hStrict g (by omega) le_rfl N hr hn hE hRank hEcard hS

/-- **`gcd(n, r) = 2`: KUM from the strict case.** -/
theorem solvesKUMAtRankSize_two_mul_of_strict {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p.Coprime q) (hStrict : SolvesStrictKUMAtRankSize α (q * 2) (p * 2)) :
    SolvesKUMAtRankSize α (q * 2) (p * 2) :=
  solvesKUMAtRankSize_mul_of_strict hp hq hpq 2 (fun g' h2 hle => by
    have h : g' = 2 := by omega
    rw [h]
    exact hStrict)

/-- **`gcd(n, r) = 2` with a tight set, in every rank.** A uniformly dense matroid of rank `2q`
on `2p` elements, `gcd(p, q) = 1`, with a nonempty proper tight set has a cyclic basis ordering.
The tight set has rank `q`; its restriction and contraction have rank `q` on `p` elements, which
is the coprime case. -/
theorem exists_cyclicBasisOrder_of_two_mul_of_nonempty_proper_tight
    (M : Matroid α) {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    (hE : M.E.Finite)
    (hRank : M.eRank = ((q * 2 : ℕ) : ℕ∞))
    (hEcard : M.E.encard = ((p * 2 : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M (p * 2) (q * 2))
    {X : Set α}
    (hX : TightRatio M (p * 2) (q * 2) X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    ∃ order : Fin (p * 2) ≃ M.E,
      CyclicBasisOrder M (q * 2) (Nat.mul_pos hp (by norm_num)) order := by
  have hDense' : UniformlyDenseRatio M p q := by
    apply UniformlyDenseRatio.unscale M p q 2 (by norm_num)
    rw [Nat.mul_comm 2 p, Nat.mul_comm 2 q]
    exact hDense
  have hX' : TightRatio M p q X := by
    apply TightRatio.unscale M p q 2 (by norm_num)
    rw [Nat.mul_comm 2 p, Nat.mul_comm 2 q]
    exact hX
  obtain ⟨a, b, ha, hb, hab, hXrank⟩ :=
    exists_tight_rank_factorization M hp hq (by norm_num) hpq hE hRank hEcard hX' hXnonempty
      hXproper
  have ha1 : a = 1 := by omega
  have hb1 : b = 1 := by omega
  subst ha1
  subst hb1
  have hcop : SolvesKUMAtRankSize α (1 * q) (1 * p) := by
    rw [Nat.one_mul, Nat.one_mul]
    exact VHT.solvesKUMAtRankSize_of_coprime hpq.symm
  have hOrder :=
    exists_cyclicBasisOrder_of_ratio_tight_of_rank_solutions
      (M := M) (X := X) (a := 1) (b := 1) (p := p) (q := q)
      Nat.one_pos Nat.one_pos hp hq hE
      (by rw [show (1 + 1) * p = p * 2 by ring]; exact hEcard)
      (by rw [show (1 + 1) * q = q * 2 by ring]; exact hRank)
      hDense' hX' hXrank hcop hcop
  exact exists_cyclicBasisOrder_congr M (by ring) (by ring) hOrder

end

end HigherRankKUM
