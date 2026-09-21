import HigherRankKUM.Rank4.GcdTwoRepairGeometry
import HigherRankKUM.Rank4.ThreePairTriangle

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open Set
open PairCycleIndexing
open Rank4ThreePairDual

variable {α : Type*}

/-- In the rank-four (`h=2`) pair-cycle model, the abstract local compatibility
relation is exactly the three-consecutive-block `middlePairRelation`.  The
left endpoint pair appears in reversed Boolean order because this is the
convention built into `AdmissiblePairCycle.localRelation`; the middle and
right pairs use their natural orders.

Keeping this equality explicit prevents label-convention drift between the
repair-state layer and the six-block parity lemmas. -/
theorem localRelation_eq_middlePairRelation
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (t : Fin N) :
    A.localRelation (by omega) t =
      middlePairRelation M
        (A.element t true) (A.element t false)
        (A.element (cyclicIndex N hN t 1) false)
        (A.element (cyclicIndex N hN t 1) true)
        (A.element (cyclicIndex N hN t 2) false)
        (A.element (cyclicIndex N hN t 2) true) := by
  let m := cyclicIndex N hN t 1
  let r := cyclicIndex N hN t 2
  have hcore : A.core t = A.block m := by
    simpa [m] using core_eq_next_block A t
  have hY : M.Indep
      ({A.element m false, A.element m true} : Set α) := by
    have hc := A.core_indep (by omega) t
    rw [hcore] at hc
    simpa [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using hc
  have hXY : Disjoint
      ({A.element t true, A.element t false} : Set α)
      ({A.element m false, A.element m true} : Set α) := by
    have h := A.block_disjoint_core (by omega) h2N t
    rw [hcore] at h
    simpa [m, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet,
      Set.pair_comm] using h
  have hYR : Disjoint
      ({A.element m false, A.element m true} : Set α)
      ({A.element r false, A.element r true} : Set α) := by
    have h := (A.endpoint_block_disjoint_core (by omega) h2N t).symm
    rw [hcore] at h
    have hr : cyclicIndex N hN t 2 = r := rfl
    simpa [m, r, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet,
      hr] using h
  have hbridge := middlePairRelation_eq_contract_crossBaseRelation M hY hXY hYR
  change
    PairCycle.crossBaseRelation (M.contract (A.core t))
        (A.element t true) (A.element t false)
        (A.element (cyclicIndex N hN t 2) false)
        (A.element (cyclicIndex N hN t 2) true) = _
  rw [hcore]
  simpa [m, r, AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet]
    using hbridge.symm

end Rank4GcdTwoRepair
end HigherRankKUM
