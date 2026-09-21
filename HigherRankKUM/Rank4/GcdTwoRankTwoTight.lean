import HigherRankKUM.RationalDensity
import HigherRankKUM.Rank4.GcdTwoRepairGeometry

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open Set

variable {α : Type*}

/-- Every pair block in an admissible rank-four (`h=2`) cycle spans a rank-two
flat. This gives the exact rank input for the closure-propagation endpoint. -/
theorem eRk_closure_block_eq_two
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (i : Fin N) :
    M.eRk (M.closure (A.block i)) = 2 := by
  have hInd : M.Indep (A.block i) :=
    (A.alignedBase i).indep.subset (A.block_subset_window (by omega) i)
  have hcard : (A.block i).encard = 2 := by
    exact Set.encard_pair (A.element_ne i)
  rw [M.eRk_closure_eq, hInd.eRk_eq_encard, hcard]

/-- If the rank-two flat spanned by one pair block reaches `N` elements, it is
exactly tight for the rank-four gcd-two density ratio `N/2`.

This is the precise endpoint wanted from a closure-propagation argument. -/
theorem tightRatio_closure_block_of_encard_eq_card
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (i : Fin N)
    (hcard : (M.closure (A.block i)).encard = (N : ℕ∞)) :
    TightRatio M N 2 (M.closure (A.block i)) := by
  refine ⟨M.closure_subset_ground (A.block i), ?_⟩
  rw [hcard, eRk_closure_block_eq_two A i]
  norm_num [mul_comm]

/-- A block closure is proper in a genuine rank-four pair-cycle: it has rank
2, while the whole matroid has rank 4. -/
theorem closure_block_ne_ground
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (i : Fin N) :
    M.closure (A.block i) ≠ M.E := by
  intro hEq
  have hr := eRk_closure_block_eq_two A i
  rw [hEq, M.eRk_ground, A.rankEq] at hr
  norm_num at hr

/-- Therefore a rank-two block closure of size `N` is a nonempty proper tight
set. Any strict `4k+2` counterexample must keep every such closure below this
capacity. -/
theorem closure_block_is_nonempty_proper_tight_of_encard_eq_card
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (i : Fin N)
    (hcard : (M.closure (A.block i)).encard = (N : ℕ∞)) :
    TightRatio M N 2 (M.closure (A.block i)) ∧
      (M.closure (A.block i)).Nonempty ∧
      M.closure (A.block i) ≠ M.E := by
  refine ⟨tightRatio_closure_block_of_encard_eq_card A i hcard, ?_,
    closure_block_ne_ground A i⟩
  exact ⟨A.element i false,
    M.subset_closure (A.block i) (A.block_subset_ground i) (by
      change A.element i false ∈ ({A.element i false, A.element i true} : Set α)
      exact Set.mem_insert _ _)⟩

end Rank4GcdTwoRepair
end HigherRankKUM