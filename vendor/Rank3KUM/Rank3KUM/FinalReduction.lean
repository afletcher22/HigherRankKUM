import Rank3KUM.TightSetReduction
import Rank3KUM.StrictDensity
import Rank3KUM.InductionStep

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
All nontrivial tight-set cases are discharged, so the full rank-three theorem
reduces exactly to the strictly dense case.
-/
theorem exists_cyclicBasisOrder3_of_strict_case
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    (hStrictCase :
      StrictlyUniformlyDense M k →
        ∃ order : Fin (3 * k) ≃ M.E,
          CyclicBasisOrder3 M (by omega) order) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  rcases
      exists_nonempty_proper_tight_or_strictlyUniformlyDense
        M k hDense with
    ⟨X, hX, hXnonempty, hXproper⟩ | hStrict
  · exact
      exists_cyclicBasisOrder3_of_nonempty_proper_tight
        M k hk hE hRank hEcard hDense
        hX hXnonempty hXproper
  · exact hStrictCase hStrict

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_strict_case

end

end Rank3KUM
