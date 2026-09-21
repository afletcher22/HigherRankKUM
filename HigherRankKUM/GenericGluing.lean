import HigherRankKUM.CyclicOrder
import HigherRankKUM.TightContraction

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
Abstract restriction/contraction gluing. If every output `(s+t)`-window
splits as a `t`-window from an ordering of `M / X` union an `s`-window from
an ordering of `M | X`, then every output window is a basis of `M`.

This theorem is rank-independent; all schedule arithmetic is isolated in the
window-decomposition hypothesis.
-/
theorem cyclicBasisOrder_of_restrict_contract_window_decomposition
    (M : Matroid α) {X : Set α}
    (hX : X ⊆ M.E)
    {s t n nS nT : ℕ}
    (hn : 0 < n) (hnS : 0 < nS) (hnT : 0 < nT)
    (σ : Fin n ≃ M.E)
    (σS : Fin nS ≃ (Matroid.restrict M X).E)
    (σT : Fin nT ≃ (Matroid.contract M X).E)
    (hS : CyclicBasisOrder (Matroid.restrict M X) s hnS σS)
    (hT : CyclicBasisOrder (Matroid.contract M X) t hnT σT)
    (hdecomp : ∀ i : Fin n,
      ∃ iS : Fin nS, ∃ iT : Fin nT,
        cyclicWindow (s + t) hn σ i =
          cyclicWindow t hnT σT iT ∪
            cyclicWindow s hnS σS iS) :
    CyclicBasisOrder M (s + t) hn σ := by
  intro i
  obtain ⟨iS, iT, hi⟩ := hdecomp i
  rw [hi]
  apply isBase_union_of_isBasis_contract_isBase M hX
  · exact (Matroid.isBase_restrict_iff hX).mp (hS iS)
  · exact hT iT

/--
A finite tight set produces two uniformly dense factors with the same density
parameter: its restriction and its contraction.
-/
theorem UniformlyDense.tight_factors
    (M : Matroid α) (k : ℕ)
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXfinite : X.Finite) :
    UniformlyDense (Matroid.restrict M X) k ∧
      UniformlyDense (Matroid.contract M X) k := by
  exact ⟨UniformlyDense.restrict M k hDense hX.1,
    UniformlyDense.contract_tight M k hDense hX hXfinite⟩

end

end HigherRankKUM
