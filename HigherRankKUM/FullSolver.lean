import HigherRankKUM.RationalDensity
import HigherRankKUM.DivisibleSolver

namespace HigherRankKUM

noncomputable section

variable {α : Type*}

/--
`SolvesKUMAtRank α r` packages full KUM at a fixed positive rank `r`:
for every finite uniformly dense rank-`r` matroid, with arbitrary positive
ground-set size `n`, there is a cyclic basis ordering.

Uniform density is expressed intrinsically using the actual size/rank ratio,
`r * |X| ≤ n * r(X)`.
-/
def SolvesKUMAtRank (α : Type*) (r : ℕ) : Prop :=
  ∀ (N : Matroid α) (n : ℕ)
    (hr : 0 < r) (hn : 0 < n)
    (_hE : N.E.Finite)
    (_hRank : N.eRank = r)
    (_hEcard : N.E.encard = (n : ℕ∞))
    (_hDense : UniformlyDenseRatio N n r),
    ∃ order : Fin n ≃ N.E,
      CyclicBasisOrder N r hn order

/-- A full fixed-rank KUM solver specializes to the existing divisible
solver interface. -/
theorem SolvesKUMAtRank.to_divisible
    {r : ℕ} (hSolve : SolvesKUMAtRank α r) :
    SolvesDivisibleKUMAtRank α r := by
  intro N k hr hk hE hRank hEcard hDense
  have hRatio : UniformlyDenseRatio N (r * k) r := by
    intro X hX
    have h := hDense X hX
    calc
      (r : ℕ∞) * X.encard ≤
          (r : ℕ∞) * ((k : ℕ∞) * N.eRk X) := by
            gcongr
      _ = ((r * k : ℕ) : ℕ∞) * N.eRk X := by
            rw [ENat.natCast_mul]
            simp [mul_assoc]
  exact hSolve N (r * k) hr (Nat.mul_pos hr hk)
    hE hRank hEcard hRatio

end

end HigherRankKUM
