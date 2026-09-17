import HigherRankKUM.Rank4.GcdTwoLabelGauge

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open Set
open BinaryRelationCycle
open PairCycle
open PairCycleIndexing
open Rank4ThreePairDual

variable {α : Type*}

/-- The rank-four local relation computed from an arbitrary Boolean labelling
of every unlabelled pair block. The left endpoint uses the same reversed-label
convention as `AdmissiblePairCycle.localRelation`. -/
def localRelationFromPairLabels
    (M : Matroid α) (N : ℕ) (hN : 0 < N)
    (x : Fin N → Bool → α) (t : Fin N) : Relation :=
  middlePairRelation M
    (x t true) (x t false)
    (x (cyclicIndex N hN t 1) false)
    (x (cyclicIndex N hN t 1) true)
    (x (cyclicIndex N hN t 2) false)
    (x (cyclicIndex N hN t 2) true)

/-- If `x` gives any Boolean labelling of the same unlabelled pair sets as an
admissible h=2 cycle `B`, then `B.localRelation` differs from the relation
system computed from `x` only by a vertex gauge.

This is stronger than `exists_localRelation_gauge_of_blocks_eq`: `x` need not
come from another admissible cycle or even from a global equivalence. -/
theorem exists_localRelation_gauge_of_pair_labels
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (B : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (x : Fin N → Bool → α)
    (hpairs : ∀ i : Fin N,
      ({x i false, x i true} : Set α) = B.block i) :
    ∃ g : Fin N → Bool, ∀ t : Fin N,
      B.localRelation (by omega) t =
        gaugeRelation (g t) (g (cyclicIndex N hN t 2))
          (localRelationFromPairLabels M N hN x t) := by
  classical
  have hxne : ∀ i : Fin N, x i false ≠ x i true := by
    intro i hEq
    have hcard : ({x i false, x i true} : Set α).encard = 2 := by
      calc
        ({x i false, x i true} : Set α).encard = (B.block i).encard := by
          rw [hpairs i]
        _ = 2 := by
          rw [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet]
          exact Set.encard_pair (B.element_ne i)
    rw [hEq] at hcard
    simp at hcard
  have hlabels : ∀ i : Fin N, ∃ p : Bool,
      B.element i false = bitPick (x i false) (x i true) p ∧
      B.element i true = bitPick (x i false) (x i true) (Bool.not p) := by
    intro i
    apply pair_labels_eq_bitPick_of_pair_eq (hxne i) (B.element_ne i)
    simpa [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      (hpairs i).symm
  choose g hgFalse hgTrue using hlabels
  refine ⟨g, ?_⟩
  intro t
  let m := cyclicIndex N hN t 1
  let r := cyclicIndex N hN t 2
  have hleftTrue :
      B.element t true = bitPick (x t true) (x t false) (g t) := by
    have h := hgTrue t
    cases g t <;> simpa [bitPick] using h
  have hleftFalse :
      B.element t false = bitPick (x t true) (x t false) (Bool.not (g t)) := by
    have h := hgFalse t
    cases g t <;> simpa [bitPick] using h
  have hmidFalse :
      B.element m false = bitPick (x m false) (x m true) (g m) := hgFalse m
  have hmidTrue :
      B.element m true = bitPick (x m false) (x m true) (Bool.not (g m)) :=
    hgTrue m
  have hrightFalse :
      B.element r false = bitPick (x r false) (x r true) (g r) := hgFalse r
  have hrightTrue :
      B.element r true = bitPick (x r false) (x r true) (Bool.not (g r)) :=
    hgTrue r
  rw [localRelation_eq_middlePairRelation B h2N t]
  change
    middlePairRelation M
        (B.element t true) (B.element t false)
        (B.element m false) (B.element m true)
        (B.element r false) (B.element r true) = _
  rw [hleftTrue, hleftFalse, hmidFalse, hmidTrue, hrightFalse, hrightTrue]
  calc
    middlePairRelation M
        (bitPick (x t true) (x t false) (g t))
        (bitPick (x t true) (x t false) (Bool.not (g t)))
        (bitPick (x m false) (x m true) (g m))
        (bitPick (x m false) (x m true) (Bool.not (g m)))
        (bitPick (x r false) (x r true) (g r))
        (bitPick (x r false) (x r true) (Bool.not (g r))) =
      middlePairRelation M
        (bitPick (x t true) (x t false) (g t))
        (bitPick (x t true) (x t false) (Bool.not (g t)))
        (x m false) (x m true)
        (bitPick (x r false) (x r true) (g r))
        (bitPick (x r false) (x r true) (Bool.not (g r))) := by
          exact middlePairRelation_relabel_middle M
            (bitPick (x t true) (x t false) (g t))
            (bitPick (x t true) (x t false) (Bool.not (g t)))
            (x m false) (x m true)
            (bitPick (x r false) (x r true) (g r))
            (bitPick (x r false) (x r true) (Bool.not (g r)))
            (g m)
    _ = relabelInput (g t)
        (relabelOutput (g r)
          (middlePairRelation M
            (x t true) (x t false)
            (x m false) (x m true)
            (x r false) (x r true))) := by
          exact middlePairRelation_relabel_endpoints M
            (x t true) (x t false)
            (x m false) (x m true)
            (x r false) (x r true)
            (g t) (g r)
    _ = gaugeRelation (g t) (g r)
        (localRelationFromPairLabels M N hN x t) := by
          rfl

/-- Compatibility-level orientability depends only on the unlabelled pair
sets, even when the comparison labels do not themselves form an admissible
pair-cycle object. -/
theorem pairRelationOrientable_iff_of_pair_labels
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (B : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (x : Fin N → Bool → α)
    (hpairs : ∀ i : Fin N,
      ({x i false, x i true} : Set α) = B.block i) :
    PairCycleObstruction.PairRelationOrientable N 2 hN
        (B.localRelation (by omega)) ↔
      PairCycleObstruction.PairRelationOrientable N 2 hN
        (localRelationFromPairLabels M N hN x) := by
  obtain ⟨g, hg⟩ :=
    exists_localRelation_gauge_of_pair_labels B h2N x hpairs
  have hfun :
      B.localRelation (by omega) =
        (fun i => gaugeRelation (g i) (g (cyclicIndex N hN i 2))
          (localRelationFromPairLabels M N hN x i)) := by
    funext i
    exact hg i
  rw [hfun]
  exact PairCycleObstruction.pairRelationOrientable_gauge_iff hN
    (localRelationFromPairLabels M N hN x) g

end Rank4GcdTwoRepair
end HigherRankKUM
