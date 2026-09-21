import HigherRankKUM.DivisibleSolver

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
A finite uniformly dense rank-one matroid on `k` elements has a generic
cyclic basis ordering: every one-element window is a basis.
-/
theorem exists_cyclicBasisOrder_of_rank_one
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 1)
    (hEcard : M.E.encard = (k : ℕ∞))
    (hDense : UniformlyDense M k) :
    ∃ order : Fin (1 * k) ≃ M.E,
      CyclicBasisOrder M 1 (Nat.mul_pos (by omega) hk) order := by
  letI : Fintype M.E := hE.fintype
  have hEncard : M.E.ncard = k := by
    have hcast : (M.E.ncard : ℕ∞) = (k : ℕ∞) := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast
  have hNatCard : Nat.card M.E = k := by
    simpa only [Nat.card_coe_set_eq] using hEncard
  let baseOrder : Fin k ≃ M.E :=
    (Finite.equivFinOfCardEq hNatCard).symm
  let order : Fin (1 * k) ≃ M.E :=
    (finCongr (by omega)).trans baseOrder
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  let : M.Loopless := hLoopless
  refine ⟨order, ?_⟩
  intro i
  have heNonloop : M.IsNonloop (order i : α) :=
    Matroid.isNonloop_of_loopless (order i).property
  have hInd : M.Indep ({(order i : α)} : Set α) :=
    heNonloop.indep
  have hBase : M.IsBase ({(order i : α)} : Set α) := by
    have hcard : ({(order i : α)} : Set α).encard = 1 := by simp
    apply hInd.isBase_of_eRk_ge (Set.finite_singleton _)
    exact
      (hRank.trans
        (hcard.symm.trans hInd.eRk_eq_encard.symm)).le
  have hset :
      cyclicWindow 1 (Nat.mul_pos (by omega) hk) order i =
        ({(order i : α)} : Set α) := by
    ext x
    simp only [cyclicWindow, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simp [cyclicIndex_zero]
    · intro hx
      subst x
      exact ⟨0, by simp [cyclicIndex_zero]⟩
  rw [hset]
  exact hBase

/-- Divisible KUM is solved in rank one. -/
theorem solvesDivisibleKUMAtRank_one :
    SolvesDivisibleKUMAtRank α 1 := by
  intro N k hr hk hE hRank hEcard hDense
  have hEcard' : N.E.encard = (k : ℕ∞) := by
    simpa using hEcard
  simpa [SolvesDivisibleKUMAtRank] using
    (exists_cyclicBasisOrder_of_rank_one
      N k hk hE hRank hEcard' hDense)

end

end HigherRankKUM
