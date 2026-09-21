import HigherRankKUM.BalancedGluing

namespace HigherRankKUM

noncomputable section

variable {α : Type*}

/--
`SolvesDivisibleKUMAtRank α r` packages the divisible uniformly-dense KUM
statement at a fixed positive rank `r`, for matroids on ambient type `α`.
-/
def SolvesDivisibleKUMAtRank (α : Type*) (r : ℕ) : Prop :=
  ∀ (N : Matroid α) (k : ℕ)
    (hr : 0 < r) (hk : 0 < k)
    (_hE : N.E.Finite)
    (_hRank : N.eRank = r)
    (_hEcard : N.E.encard = ((r * k : ℕ) : ℕ∞))
    (_hDense : UniformlyDense N k),
    ∃ order : Fin (r * k) ≃ N.E,
      CyclicBasisOrder N r (Nat.mul_pos hr hk) order

/-- Divisible KUM is solved at every positive rank strictly below `r`. -/
def SolvesDivisibleKUMBelow (α : Type*) (r : ℕ) : Prop :=
  ∀ s : ℕ, 0 < s → s < r → SolvesDivisibleKUMAtRank α s

end

end HigherRankKUM
