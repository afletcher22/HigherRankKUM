import HigherRankKUM.RationalDensity
import HigherRankKUM.DivisibleSolver

namespace HigherRankKUM

noncomputable section

variable {α : Type*}

/--
Transport existence of a cyclic basis ordering across equal natural size and
rank parameters. This packages the dependent `Fin` transport in one place so
arithmetic reductions do not rewrite through positivity proofs at call sites.
-/
theorem exists_cyclicBasisOrder_congr
    (M : Matroid α) {n n' r r' : ℕ}
    {hn : 0 < n} {hn' : 0 < n'}
    (hN : n = n') (hR : r = r')
    (hOrder : ∃ order : Fin n ≃ M.E,
      CyclicBasisOrder M r hn order) :
    ∃ order : Fin n' ≃ M.E,
      CyclicBasisOrder M r' hn' order := by
  subst n'
  subst r'
  simpa using hOrder

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
