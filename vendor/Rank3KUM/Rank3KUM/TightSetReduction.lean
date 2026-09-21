import Rank3KUM.BalancedGluing

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
Any nonempty proper tight set resolves the rank-three cyclic-order problem.
The active route passes through one balanced point-pair gluing module and uses
direct ground-set transport; the strict branch is unchanged.
-/
theorem exists_cyclicBasisOrder3_of_nonempty_proper_tight
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  exact
    exists_cyclicBasisOrder3_of_nonempty_proper_tight_gluing_clean
      M k hk hE hRank hEcard hDense hX hXnonempty hXproper

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_nonempty_proper_tight

end

end Rank3KUM
