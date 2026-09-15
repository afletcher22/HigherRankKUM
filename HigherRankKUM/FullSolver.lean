import HigherRankKUM.RationalDensity
import HigherRankKUM.DivisibleSolver

namespace HigherRankKUM

noncomputable section

variable {α : Type*}

/-- KUM at one exact rank/ground-size pair. -/
def SolvesKUMAtRankSize (α : Type*) (r n : ℕ) : Prop :=
  ∀ (N : Matroid α)
    (hr : 0 < r) (hn : 0 < n)
    (_hE : N.E.Finite)
    (_hRank : N.eRank = r)
    (_hEcard : N.E.encard = (n : ℕ∞))
    (_hDense : UniformlyDenseRatio N n r),
    ∃ order : Fin n ≃ N.E,
      CyclicBasisOrder N r hn order

/--
`SolvesKUMAtRank α r` packages full KUM at fixed rank `r`, uniformly over
all ground-set sizes. It is intentionally factored through
`SolvesKUMAtRankSize` so reductions can expose only the exact size dependency
they really need.
-/
def SolvesKUMAtRank (α : Type*) (r : ℕ) : Prop :=
  ∀ n : ℕ, SolvesKUMAtRankSize α r n

/-- Full KUM is solved at every positive rank strictly below `r`. -/
def SolvesKUMBelow (α : Type*) (r : ℕ) : Prop :=
  ∀ s : ℕ, 0 < s → s < r → SolvesKUMAtRank α s

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
  exact hSolve (r * k) N hr (Nat.mul_pos hr hk)
    hE hRank hEcard hRatio

end

end HigherRankKUM
