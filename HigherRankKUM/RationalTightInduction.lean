import HigherRankKUM.RationalTightFactorReduction

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
In a finite instance with reduced density ratio `p/q`, the rank of every
nonempty proper tight set is a nontrivial multiple of `q`.

More precisely, if the ambient rank and size are `q*g` and `p*g`, then a
nonempty proper tight set has rank `q*a` for some `0 < a < g`; writing
`b = g-a` gives positive factors `a,b` with `a+b=g`.
-/
theorem exists_tight_rank_factorization
    (M : Matroid α) {X : Set α} {p q g : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hg : 0 < g)
    (hpq : p.Coprime q)
    (hE : M.E.Finite)
    (hRank : M.eRank = ((q * g : ℕ) : ℕ∞))
    (hEcard : M.E.encard = ((p * g : ℕ) : ℕ∞))
    (hX : TightRatio M p q X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ a + b = g ∧
        M.eRk X = ((a * q : ℕ) : ℕ∞) := by
  have hXfinite : X.Finite := hE.subset hX.1
  have hrX_le : M.eRk X ≤ ((q * g : ℕ) : ℕ∞) := by
    calc
      M.eRk X ≤ M.eRank := M.eRk_le_eRank X
      _ = ((q * g : ℕ) : ℕ∞) := hRank
  obtain ⟨s, hXrank, hs_le⟩ := ENat.le_natCast_iff.mp hrX_le
  have hs_ne_zero : s ≠ 0 := by
    intro hs0
    have hrank0 : M.eRk X = ((q * 0 : ℕ) : ℕ∞) := by
      simpa [hs0] using hXrank
    have hcard0 :=
      TightRatio.encard_eq_mul_of_eRk_eq_mul
        M p q 0 hq hXfinite hX hrank0
    have hXempty : X = ∅ := Set.encard_eq_zero.mp (by simpa using hcard0)
    exact hXnonempty.ne_empty hXempty
  have hs_ne_toprank : s ≠ q * g := by
    intro hsTop
    have hrankTop : M.eRk X = ((q * g : ℕ) : ℕ∞) := by
      simpa [hsTop] using hXrank
    have hcardTop :=
      TightRatio.encard_eq_mul_of_eRk_eq_mul
        M p q g hq hXfinite hX hrankTop
    have hcard_eq : X.encard = M.E.encard := by
      calc
        X.encard = ((p * g : ℕ) : ℕ∞) := hcardTop
        _ = M.E.encard := hEcard.symm
    have hXE : X = M.E :=
      hXfinite.eq_of_subset_of_encard_le hX.1 hcard_eq.symm.le
    exact hXproper hXE
  have hs_pos : 0 < s := Nat.pos_of_ne_zero hs_ne_zero
  have hs_lt : s < q * g := by omega
  have hNatTight : q * X.ncard = p * s := by
    have htight := hX.2
    rw [← hXfinite.cast_ncard_eq, hXrank] at htight
    exact_mod_cast htight
  have hq_dvd_ps : q ∣ p * s := by
    rw [← hNatTight]
    exact Nat.dvd_mul_right q X.ncard
  have hq_dvd_s : q ∣ s :=
    hpq.symm.dvd_of_dvd_mul_left hq_dvd_ps
  obtain ⟨a, haeq⟩ := hq_dvd_s
  have ha_pos : 0 < a := by
    by_contra! ha0
    have ha_zero : a = 0 := Nat.eq_zero_of_le_zero ha0
    subst a
    simp at haeq
    exact hs_ne_zero haeq
  have ha_lt_g : a < g := by
    by_contra! hga
    have hmul : q * g ≤ q * a :=
      Nat.mul_le_mul_left q hga
    rw [← haeq] at hmul
    exact (not_le_of_gt hs_lt) hmul
  let b : ℕ := g - a
  have hb_pos : 0 < b := by
    dsimp [b]
    omega
  have hab : a + b = g := by
    dsimp [b]
    omega
  refine ⟨a, b, ha_pos, hb_pos, hab, ?_⟩
  calc
    M.eRk X = (s : ℕ∞) := hXrank
    _ = ((q * a : ℕ) : ℕ∞) := by rw [haeq]
    _ = ((a * q : ℕ) : ℕ∞) := by rw [Nat.mul_comm]

/--
Generic rational proper-tight reduction.

For a reduced ratio `p/q`, an ambient rank `q*g` instance with `p*g`
elements and a nonempty proper tight set reduces to full KUM at two positive
strictly lower ranks. The periodic gluing layer is density-free; uniform
density enters only through the factor inheritance theorem.
-/
theorem exists_cyclicBasisOrder_of_ratio_nonempty_proper_tight_of_lower_ranks
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
    (hBelow : SolvesKUMBelow α (q * g)) :
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
    hBelow (a * q) (Nat.mul_pos ha hq) hA_lt
  have hSolveB : SolvesKUMAtRank α (b * q) :=
    hBelow (b * q) (Nat.mul_pos hb hq) hB_lt
  have hOrder :=
    exists_cyclicBasisOrder_of_ratio_tight_of_rank_solutions
      (M := M) (X := X) (a := a) (b := b) (p := p) (q := q)
      ha hb hp hq hE
      (by simpa [hab, Nat.mul_comm] using hEcard)
      (by simpa [hab, Nat.mul_comm] using hRank)
      hDense hX hXrank (hSolveA (a * p)) (hSolveB (b * p))
  rw [hab] at hOrder
  simpa [Nat.mul_comm] using hOrder

end

end HigherRankKUM
