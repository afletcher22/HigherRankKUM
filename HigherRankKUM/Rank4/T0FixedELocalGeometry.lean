import HigherRankKUM.Rank4.T0FixedEState

namespace HigherRankKUM
namespace Rank4FixedELocalGeometry

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- Closure transfers across a parallel pair.

If `{e,x}` is a two-element circuit and `e` is spanned by `P`, then
`x` is also spanned by `P`.  This is the representation-free form of
replacing the omitted element by its surviving parallel mate in a local
blocker obstruction. -/
theorem mem_closure_of_parallel_pair_of_mem_closure
    {M : Matroid α} {P : Set α} {e x : α}
    (he : M.IsNonloop e)
    (hpair : M.IsCircuit ({e, x} : Set α))
    (heP : e ∈ M.closure P) :
    x ∈ M.closure P := by
  have hex : e ≠ x := by
    intro hEq
    subst x
    have hsingle : M.IsCircuit ({e} : Set α) := by
      simpa using hpair
    exact he.not_isLoop hsingle.isLoop
  have hclEq : M.closure {e} = M.closure {x} :=
    (he.closure_eq_closure_iff_isCircuit_of_ne hex).2 hpair
  have hxGround : x ∈ M.E :=
    hpair.subset_ground (by simp)
  have hxSelf : x ∈ M.closure ({x} : Set α) :=
    M.subset_closure (by
      intro y hy
      simpa using hy.trans hxGround)
      (by simp)
  have hxE : x ∈ M.closure ({e} : Set α) := by
    rw [hclEq]
    exact hxSelf
  have hsing : ({e} : Set α) ⊆ M.closure P := by
    simpa using heP
  have hxcc : x ∈ M.closure (M.closure P) :=
    M.closure_mono hsing hxE
  simpa using hxcc

/-- Combine a three-blocker run and an arbitrary two-blocker run.

The three-run produces a surviving element `x` parallel to the omitted
nonloop `e`.  The two-run produces a shared pair `P` spanning `e`.
Therefore the same pair `P` spans `x`.

This is exactly the small-circuit geometry seen in the deepest exact binary
n=10 fixed-e obstruction. -/
theorem three_run_parallel_mate_mem_closure_two_run_shared_pair
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h5n : 5 ≤ n)
    (σ : Fin n ≃ E) (e : α)
    (he : M.IsNonloop e)
    (heE : e ∉ E)
    (hCBO : CyclicBasisOrder M 4 hn σ)
    (i j : Fin n)
    (hi0 : Rank4BlockerCycle.blockerAt M hn σ e i)
    (hi1 : Rank4BlockerCycle.blockerAt M hn σ e
      (cyclicIndex n hn i 1))
    (hi2 : Rank4BlockerCycle.blockerAt M hn σ e
      (cyclicIndex n hn i 2))
    (hj0 : Rank4BlockerCycle.blockerAt M hn σ e j)
    (hj1 : Rank4BlockerCycle.blockerAt M hn σ e
      (cyclicIndex n hn j 1)) :
    (σ (cyclicIndex n hn i 2) : α) ∈
      M.closure (cyclicWindow 2 hn σ (cyclicIndex n hn j 1)) := by
  let x : α := (σ (cyclicIndex n hn i 2) : α)
  let P := cyclicWindow 2 hn σ (cyclicIndex n hn j 1)
  have hpair : M.IsCircuit ({e, x} : Set α) := by
    dsimp [x]
    exact Rank4BlockerRuns.three_consecutive_blockers_isCircuit_pair
      hn h5n σ e he heE hCBO i hi0 hi1 hi2
  have heP : e ∈ M.closure P := by
    dsimp [P]
    exact Rank4BlockerRuns.two_consecutive_blockers_mem_closure_shared_pair
      hn (by omega) σ e hCBO j hj0 hj1
  dsimp [x, P]
  exact mem_closure_of_parallel_pair_of_mem_closure he hpair heP

/-- If the parallel mate from a three-blocker run is not itself in the shared
pair of a two-blocker run, then that mate together with the pair is dependent.

This is the circuit-free form needed by later four-block rigidity arguments:
a three-run plus a separate two-run creates a rank-at-most-two concentration
on three deletion-ground elements. -/
theorem three_run_two_run_shared_triple_dep
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h5n : 5 ≤ n)
    (σ : Fin n ≃ E) (e : α)
    (he : M.IsNonloop e)
    (heE : e ∉ E)
    (hCBO : CyclicBasisOrder M 4 hn σ)
    (i j : Fin n)
    (hi0 : Rank4BlockerCycle.blockerAt M hn σ e i)
    (hi1 : Rank4BlockerCycle.blockerAt M hn σ e
      (cyclicIndex n hn i 1))
    (hi2 : Rank4BlockerCycle.blockerAt M hn σ e
      (cyclicIndex n hn i 2))
    (hj0 : Rank4BlockerCycle.blockerAt M hn σ e j)
    (hj1 : Rank4BlockerCycle.blockerAt M hn σ e
      (cyclicIndex n hn j 1))
    (hxP :
      (σ (cyclicIndex n hn i 2) : α) ∉
        cyclicWindow 2 hn σ (cyclicIndex n hn j 1)) :
    M.Dep
      (insert (σ (cyclicIndex n hn i 2) : α)
        (cyclicWindow 2 hn σ (cyclicIndex n hn j 1))) := by
  let x : α := (σ (cyclicIndex n hn i 2) : α)
  let P := cyclicWindow 2 hn σ (cyclicIndex n hn j 1)
  have hPsub :
      P ⊆ cyclicWindow 4 hn σ j := by
    dsimp [P]
    rw [cyclicWindow_two_eq, cyclicWindow_four_eq]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inr (Or.inl (by simpa [cyclicIndex_add] using hy))
    · exact Or.inr (Or.inr (Or.inl (by simpa [cyclicIndex_add] using hy)))
  have hPind : M.Indep P :=
    (hCBO j).indep.subset hPsub
  have hxcl : x ∈ M.closure P := by
    dsimp [x, P]
    exact three_run_parallel_mate_mem_closure_two_run_shared_pair
      hn h5n σ e he heE hCBO i j hi0 hi1 hi2 hj0 hj1
  have hxP' : x ∉ P := by
    simpa [x, P] using hxP
  have hdep : M.Dep (insert x P) :=
    (hPind.mem_closure_iff_of_notMem hxP').1 hxcl
  simpa [x, P] using hdep

end

end Rank4FixedELocalGeometry
end HigherRankKUM
