import HigherRankKUM.DivisibleSolver
import Rank3KUM.FinalInduction

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/-- Translate the vendored rank-three cyclic-order predicate to the generic interface. -/
theorem cyclicBasisOrder_three_of_vendored_rankThree
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E)
    (h3 : Rank3KUM.CyclicBasisOrder3 M hn σ) :
    CyclicBasisOrder M 3 hn σ := by
  intro i
  have hset :
      cyclicWindow 3 hn σ i =
        ({(σ i : α),
          (σ (cyclicIndex n hn i 1) : α),
          (σ (cyclicIndex n hn i 2) : α)} : Set α) := by
    ext x
    simp only [cyclicWindow, Set.mem_range,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [cyclicIndex_zero]
    · rintro (hx | hx | hx)
      · subst x
        exact ⟨0, by simp [cyclicIndex_zero]⟩
      · subst x
        exact ⟨1, rfl⟩
      · subst x
        exact ⟨2, rfl⟩
  rw [hset]
  simpa [HigherRankKUM.cyclicIndex, Rank3KUM.cyclicIndex] using h3 i

/-- The vendored Rank3KUM v3 theorem restated in HigherRankKUM's generic language. -/
theorem exists_cyclicBasisOrder_of_rank_three
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder M 3 (by omega) order := by
  have hDense' : Rank3KUM.UniformlyDense M k := by
    simpa [HigherRankKUM.UniformlyDense, Rank3KUM.UniformlyDense] using hDense
  obtain ⟨order, horder⟩ :=
    Rank3KUM.rankThreeKUM k M hk hE hRank hEcard hDense'
  exact ⟨order,
    cyclicBasisOrder_three_of_vendored_rankThree
      M (by omega) order horder⟩

/-- Divisible KUM is solved internally at rank three via the frozen vendored v3 proof. -/
theorem solvesDivisibleKUMAtRank_three :
    SolvesDivisibleKUMAtRank α 3 := by
  intro N k hr hk hE hRank hEcard hDense
  exact exists_cyclicBasisOrder_of_rank_three
    N k hk hE hRank hEcard hDense

end

end HigherRankKUM
