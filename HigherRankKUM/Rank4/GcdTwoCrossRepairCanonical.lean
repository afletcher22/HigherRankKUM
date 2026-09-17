import HigherRankKUM.Rank4.GcdTwoAbstractLabelGauge
import HigherRankKUM.Rank4.GcdTwoCrossRepartition
import HigherRankKUM.Rank4.GcdTwoRepairMove

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open Set
open PairCycle
open PairCycleIndexing

variable {α : Type*}

/-- The canonical common-base repair target has exactly the chosen common base
as its new left pair block. -/
theorem commonBaseRepairTarget_left_block
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    {Q : Set α}
    (hL : (leftRepairMinor A s).IsBase Q)
    (hR : (rightRepairMinor A s)✶.IsBase Q) :
    (commonBaseRepairTarget A h2N s hL hR).block
        (AdjacentRepair.leftBoundaryIndex N 2 hN s) = Q := by
  change AdmissiblePairCycle.pairSet
      (repairedPairEquiv A h2N s
        (localRepartitionOfCommonBase A h2N s hL hR))
      (AdjacentRepair.leftBoundaryIndex N 2 hN s) = Q
  rw [repairedPairEquiv_left_pairSet]
  rfl

/-- The canonical common-base repair target has the complementary pair as its
new right block. -/
theorem commonBaseRepairTarget_right_block
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    {Q : Set α}
    (hL : (leftRepairMinor A s).IsBase Q)
    (hR : (rightRepairMinor A s)✶.IsBase Q) :
    (commonBaseRepairTarget A h2N s hL hR).block
        (AdjacentRepair.rightBoundaryIndex N 2 hN s) =
      repairGround A s \ Q := by
  change AdmissiblePairCycle.pairSet
      (repairedPairEquiv A h2N s
        (localRepartitionOfCommonBase A h2N s hL hR))
      (AdjacentRepair.rightBoundaryIndex N 2 hN s) = repairGround A s \ Q
  rw [repairedPairEquiv_right_pairSet]
  rfl

/-- Every other unlabelled pair block is unchanged by the canonical common-base
repair target. -/
theorem commonBaseRepairTarget_other_block
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    {Q : Set α}
    (hL : (leftRepairMinor A s).IsBase Q)
    (hR : (rightRepairMinor A s)✶.IsBase Q)
    (k : Fin N)
    (hki : k ≠ AdjacentRepair.leftBoundaryIndex N 2 hN s)
    (hkj : k ≠ AdjacentRepair.rightBoundaryIndex N 2 hN s) :
    (commonBaseRepairTarget A h2N s hL hR).block k = A.block k := by
  change AdmissiblePairCycle.pairSet
      (repairedPairEquiv A h2N s
        (localRepartitionOfCommonBase A h2N s hL hR)) k = A.block k
  exact repairedPairEquiv_other_pairSet A h2N s
    (localRepartitionOfCommonBase A h2N s hL hR) k hki hkj

/-- Canonical Boolean labels for a cross repartition. The new left block gets
labels `(c_u,d_v)` and the new right block gets
`(c_not_u,d_not_v)`; all untouched blocks retain the old labels.

These labels are only an auxiliary relation-level object. They need not be
packaged as another global pair equivalence. -/
def crossRepairCanonicalElement
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N)
    (u v : Bool) (k : Fin N) (b : Bool) : α :=
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  if k = i then
    bitPick
      (bitPick (A.element i false) (A.element i true) u)
      (bitPick (A.element j false) (A.element j true) v) b
  else if k = j then
    bitPick
      (bitPick (A.element i false) (A.element i true) (Bool.not u))
      (bitPick (A.element j false) (A.element j true) (Bool.not v)) b
  else A.element k b

@[simp] theorem crossRepairCanonicalElement_left
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N)
    (u v b : Bool) :
    crossRepairCanonicalElement A s u v
        (AdjacentRepair.leftBoundaryIndex N 2 hN s) b =
      bitPick
        (bitPick
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true) u)
        (bitPick
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true) v) b := by
  simp [crossRepairCanonicalElement]

@[simp] theorem crossRepairCanonicalElement_right
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    (u v b : Bool) :
    crossRepairCanonicalElement A s u v
        (AdjacentRepair.rightBoundaryIndex N 2 hN s) b =
      bitPick
        (bitPick
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true)
          (Bool.not u))
        (bitPick
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true)
          (Bool.not v)) b := by
  have hji : AdjacentRepair.rightBoundaryIndex N 2 hN s ≠
      AdjacentRepair.leftBoundaryIndex N 2 hN s :=
    (modified_indices_ne h2N s).symm
  simp [crossRepairCanonicalElement, hji]

@[simp] theorem crossRepairCanonicalElement_other
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (s : Fin N)
    (u v b : Bool) (k : Fin N)
    (hki : k ≠ AdjacentRepair.leftBoundaryIndex N 2 hN s)
    (hkj : k ≠ AdjacentRepair.rightBoundaryIndex N 2 hN s) :
    crossRepairCanonicalElement A s u v k b = A.element k b := by
  simp [crossRepairCanonicalElement, hki, hkj]

/-- The canonical labels recover exactly the unlabelled blocks of the actual
(noncomputably labelled) common-base repair target. -/
theorem crossRepairCanonicalElement_pairSet_eq_target_block
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    {Q : Set α}
    (hL : (leftRepairMinor A s).IsBase Q)
    (hR : (rightRepairMinor A s)✶.IsBase Q)
    (u v : Bool)
    (hQ : Q =
      {bitPick
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true) u,
       bitPick
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true) v})
    (hcomp : repairGround A s \ Q =
      {bitPick
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true)
          (Bool.not u),
       bitPick
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true)
          (Bool.not v)})
    (k : Fin N) :
    ({crossRepairCanonicalElement A s u v k false,
      crossRepairCanonicalElement A s u v k true} : Set α) =
      (commonBaseRepairTarget A h2N s hL hR).block k := by
  let i := AdjacentRepair.leftBoundaryIndex N 2 hN s
  let j := AdjacentRepair.rightBoundaryIndex N 2 hN s
  by_cases hki : k = i
  · subst k
    rw [commonBaseRepairTarget_left_block A h2N s hL hR]
    simpa [i, j, bitPick] using hQ.symm
  by_cases hkj : k = j
  · subst k
    rw [commonBaseRepairTarget_right_block A h2N s hL hR]
    simpa [i, j, bitPick] using hcomp.symm
  · rw [commonBaseRepairTarget_other_block A h2N s hL hR k
      (by simpa [i] using hki) (by simpa [j] using hkj)]
    simp [crossRepairCanonicalElement, i, j, hki, hkj,
      AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet]

/-- The arbitrary Boolean labels chosen by `commonBaseRepairTarget` are
irrelevant: its relation-level orientability is exactly that of the canonical
cross-repair labels. -/
theorem commonBaseRepairTarget_pairRelationOrientable_iff_canonical
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    {Q : Set α}
    (hL : (leftRepairMinor A s).IsBase Q)
    (hR : (rightRepairMinor A s)✶.IsBase Q)
    (u v : Bool)
    (hQ : Q =
      {bitPick
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true) u,
       bitPick
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true) v})
    (hcomp : repairGround A s \ Q =
      {bitPick
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.leftBoundaryIndex N 2 hN s) true)
          (Bool.not u),
       bitPick
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) false)
          (A.element (AdjacentRepair.rightBoundaryIndex N 2 hN s) true)
          (Bool.not v)}) :
    PairCycleObstruction.PairRelationOrientable N 2 hN
        ((commonBaseRepairTarget A h2N s hL hR).localRelation (by omega)) ↔
      PairCycleObstruction.PairRelationOrientable N 2 hN
        (localRelationFromPairLabels M N hN
          (crossRepairCanonicalElement A s u v)) := by
  exact pairRelationOrientable_iff_of_pair_labels
    (commonBaseRepairTarget A h2N s hL hR) h2N
    (crossRepairCanonicalElement A s u v)
    (crossRepairCanonicalElement_pairSet_eq_target_block
      A h2N s hL hR u v hQ hcomp)

end Rank4GcdTwoRepair
end HigherRankKUM
