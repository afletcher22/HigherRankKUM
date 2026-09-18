import HigherRankKUM.PairRelationForcedProduct
import HigherRankKUM.Rank4.GcdTwoCrossRepairSupport
import HigherRankKUM.Rank4.CrossRepartitionLocalParity

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open PairCycle
open BinaryRelationCycle
open PairCycleIndexing
open Rank4ThreePairDual
open PairCycleObstruction

variable {α : Type*}

/-- On the four physical starts touched by a canonical cross repair, forcedness
makes the representation-free local parity theorem apply verbatim. -/
theorem canonicalCrossRepair_affected_preserve_cyclicSatisfiable
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h5N : 5 < N)
    (s : Fin N) (u v : Bool)
    (hold : ∀ t : Fin N, BijectionRelation (A.localRelation (by omega) t))
    (hnew : ∀ t : Fin N, BijectionRelation
      (localRelationFromPairLabels M N hN
        (crossRepairCanonicalElement A s u v) t)) :
    CyclicSatisfiable
        ((crossRepairAffectedStarts N hN s).map
          (A.localRelation (by omega))) ↔
      CyclicSatisfiable
        ((crossRepairAffectedStarts N hN s).map
          (localRelationFromPairLabels M N hN
            (crossRepairCanonicalElement A s u v))) := by
  have h2N : 2 < N := by omega
  let s1 := cyclicIndex N hN s 1
  let s2 := cyclicIndex N hN s 2
  let s3 := cyclicIndex N hN s 3
  let s4 := cyclicIndex N hN s 4
  let s5 := cyclicIndex N hN s 5

  have hx0 (b : Bool) :
      crossRepairCanonicalElement A s u v s b = A.element s b := by
    simpa using crossRepairCanonicalElement_offset_other A (by omega) s u v b
      (q := 0) (by omega) (by omega) (by omega)
  have hx1 (b : Bool) :
      crossRepairCanonicalElement A s u v s1 b = A.element s1 b := by
    simpa [s1] using crossRepairCanonicalElement_offset_other A (by omega) s u v b
      (q := 1) (by omega) (by omega) (by omega)
  have hx2 (b : Bool) :
      crossRepairCanonicalElement A s u v s2 b =
        bitPick
          (bitPick (A.element s2 false) (A.element s2 true) u)
          (bitPick (A.element s3 false) (A.element s3 true) v) b := by
    simpa [s2, s3, AdjacentRepair.leftBoundaryIndex,
      AdjacentRepair.rightBoundaryIndex] using
      crossRepairCanonicalElement_left A s u v b
  have hx3 (b : Bool) :
      crossRepairCanonicalElement A s u v s3 b =
        bitPick
          (bitPick (A.element s2 false) (A.element s2 true) (Bool.not u))
          (bitPick (A.element s3 false) (A.element s3 true) (Bool.not v)) b := by
    simpa [s2, s3, AdjacentRepair.leftBoundaryIndex,
      AdjacentRepair.rightBoundaryIndex] using
      crossRepairCanonicalElement_right A h2N s u v b
  have hx4 (b : Bool) :
      crossRepairCanonicalElement A s u v s4 b = A.element s4 b := by
    simpa [s4] using crossRepairCanonicalElement_offset_other A (by omega) s u v b
      (q := 4) (by omega) (by omega) (by omega)
  have hx5 (b : Bool) :
      crossRepairCanonicalElement A s u v s5 b = A.element s5 b := by
    simpa [s5] using crossRepairCanonicalElement_offset_other A (by omega) s u v b
      (q := 5) (by omega) (by omega) (by omega)

  have hR1 : BijectionRelation
      (middlePairRelation M
        (A.element s true) (A.element s false)
        (A.element s1 false) (A.element s1 true)
        (A.element s2 false) (A.element s2 true)) := by
    have h := hold s
    rw [localRelation_eq_middlePairRelation A h2N s] at h
    simpa [s1, s2] using h
  have hR2 : BijectionRelation
      (middlePairRelation M
        (A.element s1 true) (A.element s1 false)
        (A.element s2 false) (A.element s2 true)
        (A.element s3 false) (A.element s3 true)) := by
    have h := hold s1
    rw [localRelation_eq_middlePairRelation A h2N s1] at h
    simpa [s1, s2, s3, cyclicIndex_add] using h
  have hR3 : BijectionRelation
      (middlePairRelation M
        (A.element s2 true) (A.element s2 false)
        (A.element s3 false) (A.element s3 true)
        (A.element s4 false) (A.element s4 true)) := by
    have h := hold s2
    rw [localRelation_eq_middlePairRelation A h2N s2] at h
    simpa [s2, s3, s4, cyclicIndex_add] using h
  have hR4 : BijectionRelation
      (middlePairRelation M
        (A.element s3 true) (A.element s3 false)
        (A.element s4 false) (A.element s4 true)
        (A.element s5 false) (A.element s5 true)) := by
    have h := hold s3
    rw [localRelation_eq_middlePairRelation A h2N s3] at h
    simpa [s3, s4, s5, cyclicIndex_add] using h

  have hS1 : BijectionRelation
      (middlePairRelation M
        (A.element s true) (A.element s false)
        (A.element s1 false) (A.element s1 true)
        (bitPick (A.element s2 false) (A.element s2 true) u)
        (bitPick (A.element s3 false) (A.element s3 true) v)) := by
    have h := hnew s
    simp only [localRelationFromPairLabels] at h
    rw [hx0 true, hx0 false, hx1 false, hx1 true, hx2 false, hx2 true] at h
    simpa [bitPick] using h
  have hS2 : BijectionRelation
      (middlePairRelation M
        (A.element s1 true) (A.element s1 false)
        (bitPick (A.element s2 false) (A.element s2 true) u)
        (bitPick (A.element s3 false) (A.element s3 true) v)
        (bitPick (A.element s2 false) (A.element s2 true) (Bool.not u))
        (bitPick (A.element s3 false) (A.element s3 true) (Bool.not v))) := by
    have h := hnew s1
    simp only [localRelationFromPairLabels] at h
    have hm : cyclicIndex N hN s1 1 = s2 := by
      simp [s1, s2, cyclicIndex_add]
    have hr : cyclicIndex N hN s1 2 = s3 := by
      simp [s1, s3, cyclicIndex_add]
    rw [hm, hr, hx1 true, hx1 false, hx2 false, hx2 true, hx3 false, hx3 true] at h
    simpa [bitPick] using h
  have hS3 : BijectionRelation
      (middlePairRelation M
        (bitPick (A.element s3 false) (A.element s3 true) v)
        (bitPick (A.element s2 false) (A.element s2 true) u)
        (bitPick (A.element s2 false) (A.element s2 true) (Bool.not u))
        (bitPick (A.element s3 false) (A.element s3 true) (Bool.not v))
        (A.element s4 false) (A.element s4 true)) := by
    have h := hnew s2
    simp only [localRelationFromPairLabels] at h
    have hm : cyclicIndex N hN s2 1 = s3 := by
      simp [s2, s3, cyclicIndex_add]
    have hr : cyclicIndex N hN s2 2 = s4 := by
      simp [s2, s4, cyclicIndex_add]
    rw [hm, hr, hx2 true, hx2 false, hx3 false, hx3 true, hx4 false, hx4 true] at h
    simpa [bitPick] using h
  have hS4 : BijectionRelation
      (middlePairRelation M
        (bitPick (A.element s3 false) (A.element s3 true) (Bool.not v))
        (bitPick (A.element s2 false) (A.element s2 true) (Bool.not u))
        (A.element s4 false) (A.element s4 true)
        (A.element s5 false) (A.element s5 true)) := by
    have h := hnew s3
    simp only [localRelationFromPairLabels] at h
    have hm : cyclicIndex N hN s3 1 = s4 := by
      simp [s3, s4, cyclicIndex_add]
    have hr : cyclicIndex N hN s3 2 = s5 := by
      simp [s3, s5, cyclicIndex_add]
    rw [hm, hr, hx3 true, hx3 false, hx4 false, hx4 true, hx5 false, hx5 true] at h
    simpa [bitPick] using h

  have hcross :=
    crossRepartition_localRelations_preserve_cyclicSatisfiable M u v
      hR1 hR2 hR3 hR4 hS1 hS2 hS3 hS4

  simpa [crossRepairAffectedStarts,
    localRelation_eq_middlePairRelation A h2N,
    localRelationFromPairLabels,
    s1, s2, s3, s4, s5, cyclicIndex_add,
    hx0, hx1, hx2, hx3, hx4, hx5, bitPick] using hcross

/-- A forced canonical cross repair cannot change global relation-level
orientability in the rank-four gcd-two regime. Any cross repair that escapes a
forced obstruction must therefore create local slack. -/
theorem canonicalCrossRepair_preserves_pairRelationOrientable_of_forced
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h5N : 5 < N)
    (hcop : Nat.gcd N 2 = 1) (s : Fin N) (u v : Bool)
    (hold : ∀ t : Fin N, BijectionRelation (A.localRelation (by omega) t))
    (hnew : ∀ t : Fin N, BijectionRelation
      (localRelationFromPairLabels M N hN
        (crossRepairCanonicalElement A s u v) t)) :
    PairRelationOrientable N 2 hN (A.localRelation (by omega)) ↔
      PairRelationOrientable N 2 hN
        (localRelationFromPairLabels M N hN
          (crossRepairCanonicalElement A s u v)) := by
  have h2N : 2 < N := by omega
  exact pairRelationOrientable_iff_of_index_replacement
    hN hcop
    (A.localRelation (by omega))
    (localRelationFromPairLabels M N hN
      (crossRepairCanonicalElement A s u v))
    (crossRepairAffectedStarts N hN s)
    (crossRepairAffectedStarts_nodup (by omega) s)
    hold hnew
    (fun t ht => localRelationFromCrossRepair_eq_old_of_not_mem_affected
      A h2N s t u v ht)
    (canonicalCrossRepair_affected_preserve_cyclicSatisfiable
      A h5N s u v hold hnew)

end Rank4GcdTwoRepair
end HigherRankKUM