import HigherRankKUM.PairRelationOrbitGauge
import HigherRankKUM.Rank4.GcdTwoMiddlePairRelation
import HigherRankKUM.Rank4.MiddlePairRelabel

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

open BinaryRelationCycle
open PairCycle
open PairCycleIndexing
open Rank4ThreePairDual

variable {α : Type*}

/-- Two rank-four admissible pair cycles with the same unlabelled pair blocks
have local Boolean relations differing only by vertex gauges. The gauge at a
block records whether the second cycle chose the same Boolean labelling of
that pair or the swapped labelling.

This is the formal choice-independence statement needed for repaired pair
cycles, whose pair equivalence deliberately chooses labels noncomputably. -/
theorem exists_localRelation_gauge_of_blocks_eq
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A B : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (hblocks : ∀ i : Fin N, B.block i = A.block i) :
    ∃ g : Fin N → Bool, ∀ t : Fin N,
      B.localRelation (by omega) t =
        gaugeRelation (g t) (g (cyclicIndex N hN t 2))
          (A.localRelation (by omega) t) := by
  classical
  have hlabels : ∀ i : Fin N, ∃ p : Bool,
      B.element i false = bitPick (A.element i false) (A.element i true) p ∧
      B.element i true =
        bitPick (A.element i false) (A.element i true) (Bool.not p) := by
    intro i
    exact pair_labels_eq_bitPick_of_pair_eq
      (A.element_ne i) (B.element_ne i) (by
        simpa [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet]
          using hblocks i)
  choose g hgFalse hgTrue using hlabels
  refine ⟨g, ?_⟩
  intro t
  let m := cyclicIndex N hN t 1
  let r := cyclicIndex N hN t 2
  have hleftTrue :
      B.element t true =
        bitPick (A.element t true) (A.element t false) (g t) := by
    have h := hgTrue t
    cases g t <;> simpa [bitPick] using h
  have hleftFalse :
      B.element t false =
        bitPick (A.element t true) (A.element t false) (Bool.not (g t)) := by
    have h := hgFalse t
    cases g t <;> simpa [bitPick] using h
  have hmidFalse :
      B.element m false =
        bitPick (A.element m false) (A.element m true) (g m) := hgFalse m
  have hmidTrue :
      B.element m true =
        bitPick (A.element m false) (A.element m true) (Bool.not (g m)) :=
    hgTrue m
  have hrightFalse :
      B.element r false =
        bitPick (A.element r false) (A.element r true) (g r) := hgFalse r
  have hrightTrue :
      B.element r true =
        bitPick (A.element r false) (A.element r true) (Bool.not (g r)) :=
    hgTrue r
  rw [localRelation_eq_middlePairRelation B h2N t,
    localRelation_eq_middlePairRelation A h2N t]
  change
    middlePairRelation M
        (B.element t true) (B.element t false)
        (B.element m false) (B.element m true)
        (B.element r false) (B.element r true) = _
  rw [hleftTrue, hleftFalse, hmidFalse, hmidTrue, hrightFalse, hrightTrue]
  calc
    middlePairRelation M
        (bitPick (A.element t true) (A.element t false) (g t))
        (bitPick (A.element t true) (A.element t false) (Bool.not (g t)))
        (bitPick (A.element m false) (A.element m true) (g m))
        (bitPick (A.element m false) (A.element m true) (Bool.not (g m)))
        (bitPick (A.element r false) (A.element r true) (g r))
        (bitPick (A.element r false) (A.element r true) (Bool.not (g r))) =
      middlePairRelation M
        (bitPick (A.element t true) (A.element t false) (g t))
        (bitPick (A.element t true) (A.element t false) (Bool.not (g t)))
        (A.element m false) (A.element m true)
        (bitPick (A.element r false) (A.element r true) (g r))
        (bitPick (A.element r false) (A.element r true) (Bool.not (g r))) := by
          exact middlePairRelation_relabel_middle M
            (bitPick (A.element t true) (A.element t false) (g t))
            (bitPick (A.element t true) (A.element t false) (Bool.not (g t)))
            (A.element m false) (A.element m true)
            (bitPick (A.element r false) (A.element r true) (g r))
            (bitPick (A.element r false) (A.element r true) (Bool.not (g r)))
            (g m)
    _ = relabelInput (g t)
        (relabelOutput (g r)
          (middlePairRelation M
            (A.element t true) (A.element t false)
            (A.element m false) (A.element m true)
            (A.element r false) (A.element r true))) := by
          exact middlePairRelation_relabel_endpoints M
            (A.element t true) (A.element t false)
            (A.element m false) (A.element m true)
            (A.element r false) (A.element r true)
            (g t) (g r)
    _ = gaugeRelation (g t) (g r)
        (middlePairRelation M
          (A.element t true) (A.element t false)
          (A.element m false) (A.element m true)
          (A.element r false) (A.element r true)) := rfl

/-- Changing only the Boolean labels inside the pair blocks of a rank-four
admissible pair cycle cannot change compatibility-level orientability. -/
theorem pairRelationOrientable_iff_of_blocks_eq
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A B : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N)
    (hblocks : ∀ i : Fin N, B.block i = A.block i) :
    PairCycleObstruction.PairRelationOrientable N 2 hN
        (B.localRelation (by omega)) ↔
      PairCycleObstruction.PairRelationOrientable N 2 hN
        (A.localRelation (by omega)) := by
  obtain ⟨g, hg⟩ := exists_localRelation_gauge_of_blocks_eq A B h2N hblocks
  have hfun :
      B.localRelation (by omega) =
        (fun i => gaugeRelation (g i) (g (cyclicIndex N hN i 2))
          (A.localRelation (by omega) i)) := by
    funext i
    exact hg i
  rw [hfun]
  exact PairCycleObstruction.pairRelationOrientable_gauge_iff hN
    (A.localRelation (by omega)) g

end Rank4GcdTwoRepair
end HigherRankKUM
