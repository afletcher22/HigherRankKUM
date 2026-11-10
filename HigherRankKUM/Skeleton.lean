import HigherRankKUM.Duality
import HigherRankKUM.RationalTightInduction
import HigherRankKUM.StrictDensity
import HigherRankKUM.VHT.Theorem21

/-!
# The rank-`r` skeleton

Given KUM at every rank below `r`, three generic reductions settle most of rank `r`:

* `gcd(r, n) = 1`: coprime KUM (van den Heuvel–Thomassé);
* `n < 2r`: duality, since the dual has rank `n - r < r`;
* a nonempty proper tight set: the rational tight reduction, which glues cyclic basis orderings
  of the restriction and the contraction.

What is left is the **strict** case with `n ≥ 2r` and `gcd(r, n) > 1`
(`solvesKUMAtRank_of_strict_large`).

The tight reduction only needs the lower ranks that a tight set can have: the multiples of
`r / gcd(n, r)` (`exists_cyclicBasisOrder_of_nonempty_proper_tight_of_multiples`).
-/

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/-- Strict KUM at one rank/ground-size pair: the matroids with no nonempty proper tight set. -/
def SolvesStrictKUMAtRankSize (α : Type*) (r n : ℕ) : Prop :=
  ∀ (N : Matroid α)
    (_hr : 0 < r) (hn : 0 < n)
    (_hE : N.E.Finite)
    (_hRank : N.eRank = r)
    (_hEcard : N.E.encard = (n : ℕ∞))
    (_hStrict : StrictlyUniformlyDenseRatio N n r),
    ∃ order : Fin n ≃ N.E,
      CyclicBasisOrder N r hn order

/-- KUM at rank `r` and size `n < r` holds vacuously: the rank is at most the size. -/
theorem solvesKUMAtRankSize_of_lt {r n : ℕ} (h : n < r) : SolvesKUMAtRankSize α r n := by
  intro N _hr _hn _hE hRank hEcard _hDense
  exfalso
  have hle := N.eRk_le_encard N.E
  rw [N.eRk_ground, hRank, hEcard] at hle
  have hle' : r ≤ n := by exact_mod_cast hle
  omega

/-- KUM at rank `r` and every size `n < 2r`, from KUM at the lower ranks, by duality. -/
theorem solvesKUMAtRankSize_of_lt_two_mul {r n : ℕ} (hBelow : SolvesKUMBelow α r)
    (h : n < 2 * r) : SolvesKUMAtRankSize α r n := by
  rcases Nat.lt_trichotomy n r with hlt | heq | hgt
  · exact solvesKUMAtRankSize_of_lt hlt
  · rw [heq]
    exact solvesKUMAtRankSize_self r
  · exact SolvesKUMAtRankSize.of_dual hgt (hBelow (n - r) (by omega) (by omega) n)

/-- The rational tight reduction, with its lower-rank input restricted to the ranks a tight set
can have: the multiples of `q`, for the reduced density ratio `p / q`. -/
theorem exists_cyclicBasisOrder_of_ratio_nonempty_proper_tight_of_multiples
    (M : Matroid α) (p q g : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hg : 0 < g)
    (hpq : p.Coprime q)
    (hE : M.E.Finite)
    (hRank : M.eRank = ((q * g : ℕ) : ℕ∞))
    (hEcard : M.E.encard = ((p * g : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M p q)
    {X : Set α}
    (hX : TightRatio M p q X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E)
    (hBelow : ∀ s, 0 < s → s < q * g → q ∣ s → SolvesKUMAtRank α s) :
    ∃ order : Fin (p * g) ≃ M.E,
      CyclicBasisOrder M (q * g) (Nat.mul_pos hp hg) order := by
  obtain ⟨a, b, ha, hb, hab, hXrank⟩ :=
    exists_tight_rank_factorization
      M hp hq hg hpq hE hRank hEcard hX hXnonempty hXproper
  have hA_lt : a * q < q * g := by
    have ha_lt : a < g := by omega
    simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left ha_lt hq
  have hB_lt : b * q < q * g := by
    have hb_lt : b < g := by omega
    simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left hb_lt hq
  have hSolveA : SolvesKUMAtRank α (a * q) :=
    hBelow (a * q) (Nat.mul_pos ha hq) hA_lt (dvd_mul_left q a)
  have hSolveB : SolvesKUMAtRank α (b * q) :=
    hBelow (b * q) (Nat.mul_pos hb hq) hB_lt (dvd_mul_left q b)
  have hOrder :=
    exists_cyclicBasisOrder_of_ratio_tight_of_rank_solutions
      (M := M) (X := X) (a := a) (b := b) (p := p) (q := q)
      ha hb hp hq hE
      (by simpa [hab, Nat.mul_comm] using hEcard)
      (by simpa [hab, Nat.mul_comm] using hRank)
      hDense hX hXrank (hSolveA (a * p)) (hSolveB (b * p))
  subst g
  exact exists_cyclicBasisOrder_congr M
    (Nat.mul_comm (a + b) p) (Nat.mul_comm (a + b) q) hOrder

/-- **The tight reduction at rank `r` and size `n`.** A uniformly dense matroid with a nonempty
proper tight set has a cyclic basis ordering, given KUM at the lower ranks that are multiples of
`r / gcd(n, r)`. -/
theorem exists_cyclicBasisOrder_of_nonempty_proper_tight_of_multiples
    (M : Matroid α) {r n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hE : M.E.Finite)
    (hRank : M.eRank = (r : ℕ∞))
    (hEcard : M.E.encard = (n : ℕ∞))
    (hDense : UniformlyDenseRatio M n r)
    {X : Set α}
    (hX : TightRatio M n r X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E)
    (hBelow : ∀ s, 0 < s → s < r → (r / Nat.gcd n r) ∣ s → SolvesKUMAtRank α s) :
    ∃ order : Fin n ≃ M.E, CyclicBasisOrder M r hn order := by
  have hg : 0 < Nat.gcd n r := Nat.gcd_pos_of_pos_left r hn
  have hpq : (n / Nat.gcd n r).Coprime (r / Nat.gcd n r) := Nat.coprime_div_gcd_div_gcd hg
  have hpg : n / Nat.gcd n r * Nat.gcd n r = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n r)
  have hqg : r / Nat.gcd n r * Nat.gcd n r = r := Nat.div_mul_cancel (Nat.gcd_dvd_right n r)
  generalize n / Nat.gcd n r = p at hpq hpg
  generalize r / Nat.gcd n r = q at hpq hqg hBelow
  generalize Nat.gcd n r = g at hg hpg hqg
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.zero_mul] at hpg
      omega
    · exact h
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, Nat.zero_mul] at hqg
      omega
    · exact h
  subst hpg
  subst hqg
  have hDense' : UniformlyDenseRatio M p q := by
    apply UniformlyDenseRatio.unscale M p q g hg
    rw [Nat.mul_comm g p, Nat.mul_comm g q]
    exact hDense
  have hX' : TightRatio M p q X := by
    apply TightRatio.unscale M p q g hg
    rw [Nat.mul_comm g p, Nat.mul_comm g q]
    exact hX
  exact exists_cyclicBasisOrder_of_ratio_nonempty_proper_tight_of_multiples M p q g hp hq hg hpq
    hE hRank hEcard hDense' hX' hXnonempty hXproper hBelow

/-- The tight reduction at rank `r` and size `n`, from KUM at every lower rank. -/
theorem exists_cyclicBasisOrder_of_nonempty_proper_tight_of_below
    (M : Matroid α) {r n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hE : M.E.Finite)
    (hRank : M.eRank = (r : ℕ∞))
    (hEcard : M.E.encard = (n : ℕ∞))
    (hDense : UniformlyDenseRatio M n r)
    {X : Set α}
    (hX : TightRatio M n r X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E)
    (hBelow : SolvesKUMBelow α r) :
    ∃ order : Fin n ≃ M.E, CyclicBasisOrder M r hn order :=
  exists_cyclicBasisOrder_of_nonempty_proper_tight_of_multiples M hr hn hE hRank hEcard hDense
    hX hXnonempty hXproper (fun s hs hsr _ => hBelow s hs hsr)

/-- KUM at `(r, n)` from the strict case at `(r, n)` and KUM at the lower ranks. -/
theorem solvesKUMAtRankSize_of_strict {r n : ℕ} (hBelow : SolvesKUMBelow α r)
    (hStrict : SolvesStrictKUMAtRankSize α r n) : SolvesKUMAtRankSize α r n := by
  intro N hr hn hE hRank hEcard hDense
  by_cases htight : ∃ X, TightRatio N n r X ∧ X.Nonempty ∧ X ≠ N.E
  · obtain ⟨X, hX, hne, hprop⟩ := htight
    exact exists_cyclicBasisOrder_of_nonempty_proper_tight_of_below N hr hn hE hRank hEcard
      hDense hX hne hprop hBelow
  · have hS : StrictlyUniformlyDenseRatio N n r := fun X hX hne hprop =>
      lt_of_le_of_ne (hDense X hX) fun heq => htight ⟨X, ⟨hX, heq⟩, hne, hprop⟩
    exact hStrict N hr hn hE hRank hEcard hS

/-- **The rank-`r` skeleton.** Given KUM at every rank below `r`, KUM at rank `r` follows from
its strict case at the sizes `n ≥ 2r` with `gcd(r, n) > 1`. -/
theorem solvesKUMAtRank_of_strict_large {r : ℕ} (hBelow : SolvesKUMBelow α r)
    (hStrict : ∀ n, 2 * r ≤ n → ¬ Nat.Coprime r n → SolvesStrictKUMAtRankSize α r n) :
    SolvesKUMAtRank α r := by
  intro n
  by_cases hcop : Nat.Coprime r n
  · exact VHT.solvesKUMAtRankSize_of_coprime hcop
  rcases Nat.lt_or_ge n (2 * r) with hsmall | hlarge
  · exact solvesKUMAtRankSize_of_lt_two_mul hBelow hsmall
  · exact solvesKUMAtRankSize_of_strict hBelow (hStrict n hlarge hcop)

end

end HigherRankKUM
