import HigherRankKUM.RationalTightFactorReduction

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
Rank-four `4k+2` proper-tight reduction with its remaining formal dependency
made explicit.

At reduced density ratio `(2k+1)/2`, every nonempty proper tight set has rank
2 and size `2k+1`; restriction and contraction are therefore both rank-two
instances of that same odd size. A full rank-two KUM solver closes both
factors, after which periodic gluing gives rank four.

HigherRankKUM currently proves only divisible rank-two KUM, so `hSolve2` is
an explicit hypothesis rather than an internal theorem.
-/
theorem exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight
    (M : Matroid α) (k : ℕ)
    (hE : M.E.Finite)
    (hRank : M.eRank = 4)
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M (2 * k + 1) 2)
    {X : Set α}
    (hX : TightRatio M (2 * k + 1) 2 X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E)
    (hSolve2 : SolvesKUMAtRank α 2) :
    ∃ order : Fin (4 * k + 2) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) order := by
  have hp : 0 < 2 * k + 1 := by omega
  obtain ⟨a, b, ha, hb, hab, hXrank⟩ :=
    exists_tight_rank_factorization
      (M := M) (X := X) (p := 2 * k + 1) (q := 2) (g := 2)
      hp (by omega) (by omega) (by omega)
      hE
      (by simpa using hRank)
      (by
        calc
          M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞) := hEcard
          _ = (((2 * k + 1) * 2 : ℕ) : ℕ∞) := by ring_nf)
      hX hXnonempty hXproper
  have ha1 : a = 1 := by omega
  have hb1 : b = 1 := by omega
  subst a
  subst b
  have hOrder :=
    exists_cyclicBasisOrder_of_ratio_tight_of_rank_solutions
      (M := M) (X := X)
      (a := 1) (b := 1) (p := 2 * k + 1) (q := 2)
      (by omega) (by omega) hp (by omega) hE
      (by
        calc
          M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞) := hEcard
          _ = (((1 + 1) * (2 * k + 1) : ℕ) : ℕ∞) := by ring_nf)
      (by simpa using hRank)
      hDense hX
      (by simpa using hXrank)
      hSolve2 hSolve2
  simpa [Nat.add_mul, Nat.mul_add] using hOrder

end

end HigherRankKUM
