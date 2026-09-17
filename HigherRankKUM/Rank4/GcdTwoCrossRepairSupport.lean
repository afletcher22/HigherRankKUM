import HigherRankKUM.Rank4.GcdTwoCrossRepairCanonical

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open PairCycleIndexing

variable {α : Type*}

/-- The four physical local-relation starts affected when blocks `s+2` and
`s+3` are repartitioned. -/
def crossRepairAffectedStarts
    (N : ℕ) (hN : 0 < N) (s : Fin N) : List (Fin N) :=
  [s,
   cyclicIndex N hN s 1,
   cyclicIndex N hN s 2,
   cyclicIndex N hN s 3]

/-- For `N > 3`, the four starts touched by a rank-four adjacent repair are
distinct. -/
theorem crossRepairAffectedStarts_nodup
    {N : ℕ} {hN : 0 < N} (h3N : 3 < N) (s : Fin N) :
    (crossRepairAffectedStarts N hN s).Nodup := by
  let s1 := cyclicIndex N hN s 1
  let s2 := cyclicIndex N hN s 2
  let s3 := cyclicIndex N hN s 3
  have h01 : s ≠ s1 := by
    intro h
    exact (cyclicIndex_ne_self_of_pos_of_lt N hN s (by omega) (by omega)) h.symm
  have h02 : s ≠ s2 := by
    intro h
    exact (cyclicIndex_ne_self_of_pos_of_lt N hN s (by omega) (by omega)) h.symm
  have h03 : s ≠ s3 := by
    intro h
    exact (cyclicIndex_ne_self_of_pos_of_lt N hN s (by omega) h3N) h.symm
  have hs1s2 : s1 ≠ s2 := by
    intro h
    have hstep := cyclicIndex_ne_self_of_pos_of_lt N hN s1 (by omega) (by omega)
    apply hstep
    change cyclicIndex N hN (cyclicIndex N hN s 1) 1 =
      cyclicIndex N hN s 1
    rw [cyclicIndex_add]
    simpa [s1, s2] using h.symm
  have hs1s3 : s1 ≠ s3 := by
    intro h
    have hstep := cyclicIndex_ne_self_of_pos_of_lt N hN s1 (by omega) (by omega)
    apply hstep
    change cyclicIndex N hN (cyclicIndex N hN s 1) 2 =
      cyclicIndex N hN s 1
    rw [cyclicIndex_add]
    simpa [s1, s3] using h.symm
  have hs2s3 : s2 ≠ s3 := by
    intro h
    have hstep := cyclicIndex_ne_self_of_pos_of_lt N hN s2 (by omega) (by omega)
    apply hstep
    change cyclicIndex N hN (cyclicIndex N hN s 2) 1 =
      cyclicIndex N hN s 2
    rw [cyclicIndex_add]
    simpa [s2, s3] using h.symm
  simp [crossRepairAffectedStarts, s1, s2, s3,
    h01, h02, h03, hs1s2, hs1s3, hs2s3]

/-- Away from the four starts whose three-block windows meet the repaired pair
blocks, the canonical cross-repair local relation is literally the old local
relation. -/
theorem localRelationFromCrossRepair_eq_old_of_not_mem_affected
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (s t : Fin N) (u v : Bool)
    (ht : t ∉ crossRepairAffectedStarts N hN s) :
    localRelationFromPairLabels M N hN
        (crossRepairCanonicalElement A s u v) t =
      A.localRelation (by omega) t := by
  let s1 := cyclicIndex N hN s 1
  let i := cyclicIndex N hN s 2
  let j := cyclicIndex N hN s 3
  have ht0 : t ≠ s := by
    intro h
    apply ht
    simp [crossRepairAffectedStarts, h]
  have ht1 : t ≠ s1 := by
    intro h
    apply ht
    simp [crossRepairAffectedStarts, s1, h]
  have hti : t ≠ i := by
    intro h
    apply ht
    simp [crossRepairAffectedStarts, i, h]
  have htj : t ≠ j := by
    intro h
    apply ht
    simp [crossRepairAffectedStarts, j, h]
  have hnext_i : cyclicIndex N hN t 1 ≠ i := by
    intro h
    apply ht1
    apply cyclicIndex_injective_start N hN 1
    calc
      cyclicIndex N hN t 1 = i := h
      _ = cyclicIndex N hN s1 1 := by
        simp [s1, i, cyclicIndex_add]
  have hnext_j : cyclicIndex N hN t 1 ≠ j := by
    intro h
    apply hti
    apply cyclicIndex_injective_start N hN 1
    calc
      cyclicIndex N hN t 1 = j := h
      _ = cyclicIndex N hN i 1 := by
        simp [i, j, cyclicIndex_add]
  have htwo_i : cyclicIndex N hN t 2 ≠ i := by
    intro h
    apply ht0
    apply cyclicIndex_injective_start N hN 2
    calc
      cyclicIndex N hN t 2 = i := h
      _ = cyclicIndex N hN s 2 := rfl
  have htwo_j : cyclicIndex N hN t 2 ≠ j := by
    intro h
    apply ht1
    apply cyclicIndex_injective_start N hN 2
    calc
      cyclicIndex N hN t 2 = j := h
      _ = cyclicIndex N hN s1 2 := by
        simp [s1, j, cyclicIndex_add]
  rw [localRelation_eq_middlePairRelation A h2N t]
  simp [localRelationFromPairLabels, crossRepairCanonicalElement,
    AdjacentRepair.leftBoundaryIndex, AdjacentRepair.rightBoundaryIndex,
    i, j, hti, htj, hnext_i, hnext_j, htwo_i, htwo_j]

end Rank4GcdTwoRepair
end HigherRankKUM
