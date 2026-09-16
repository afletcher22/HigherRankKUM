import HigherRankKUM.Rank4.GcdTwoRepairAdmissible
import HigherRankKUM.Rank4.GcdTwoClosurePotential
import HigherRankKUM.PairCycleObstruction

namespace HigherRankKUM
namespace Rank4GcdTwoRepair

variable {α : Type*}

/-- The repaired admissible pair-cycle state determined canonically by a
common base of the two local rank-two repair minors.  This packages the full
bridge

`common base -> LocalRepartition -> repaired AdmissiblePairCycle.Data`.
-/
noncomputable def commonBaseRepairTarget
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    {Q : Set α}
    (hL : (leftRepairMinor A s).IsBase Q)
    (hR : (rightRepairMinor A s)✶.IsBase Q) :
    AdmissiblePairCycle.Data M N 2 hN :=
  repairedAdmissiblePairCycle A h2N s
    (localRepartitionOfCommonBase A h2N s hL hR)

/-- One legal state transition in the rank-four gcd-two repair graph.  The
move relation deliberately remembers only that some legal local repartition
was used; it is independent of the arbitrary Boolean labels chosen inside the
new pair blocks. -/
def RepairMove
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (h2N : 2 < N)
    (A B : AdmissiblePairCycle.Data M N 2 hN) : Prop :=
  ∃ s : Fin N, ∃ R : LocalRepartition A s,
    B = repairedAdmissiblePairCycle A h2N s R

/-- Every common-base repair gives one edge of the abstract repair graph. -/
theorem repairMove_commonBaseRepairTarget
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) (h2N : 2 < N) (s : Fin N)
    {Q : Set α}
    (hL : (leftRepairMinor A s).IsBase Q)
    (hR : (rightRepairMinor A s)✶.IsBase Q) :
    RepairMove h2N A (commonBaseRepairTarget A h2N s hL hR) := by
  refine ⟨s, localRepartitionOfCommonBase A h2N s hL hR, ?_⟩
  rfl

/-- Orientability of one admissible pair-cycle state at the Boolean relation
level.  In the gcd-two rank-four regime this is the `h=2` local-relation cycle
used by the Sprint 2 obstruction theorem. -/
def RelationOrientable
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN) : Prop :=
  PairCycleObstruction.PairRelationOrientable N 2 hN
    (A.localRelation (by omega))

/-- The exact remaining termination reduction for the closure-potential
strategy.  If every non-orientable admissible pair-cycle admits one legal
repair with strictly larger closure potential, then bounded strict ascent
forces eventual reachability of a relation-orientable state.

Thus all termination bookkeeping is discharged here; the remaining hard
matroid statement is precisely the local strict-ascent hypothesis `hascent`. -/
theorem exists_reachable_relationOrientable_of_strict_closure_ascent
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (h2N : 2 < N)
    (hascent : ∀ A : AdmissiblePairCycle.Data M N 2 hN,
      ¬ RelationOrientable A →
      ∃ B : AdmissiblePairCycle.Data M N 2 hN,
        RepairMove h2N A B ∧ closurePotential A < closurePotential B) :
    ∀ A : AdmissiblePairCycle.Data M N 2 hN,
      ∃ B : AdmissiblePairCycle.Data M N 2 hN,
        Relation.ReflTransGen (RepairMove h2N) A B ∧ RelationOrientable B := by
  exact PotentialAscent.exists_reachable_good_of_bounded_strict_ascent
    (RepairMove h2N) RelationOrientable closurePotential (4 * N)
    (fun A => closurePotential_le_four_mul A) hascent

/-- Local-maximum version of the same reduction: under the strict-ascent
hypothesis, any state from which no legal repair raises the closure potential
is already relation-orientable. -/
theorem relationOrientable_of_no_closure_ascent
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (h2N : 2 < N)
    (hascent : ∀ A : AdmissiblePairCycle.Data M N 2 hN,
      ¬ RelationOrientable A →
      ∃ B : AdmissiblePairCycle.Data M N 2 hN,
        RepairMove h2N A B ∧ closurePotential A < closurePotential B)
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (hmax : ∀ B, RepairMove h2N A B → closurePotential B ≤ closurePotential A) :
    RelationOrientable A := by
  exact PotentialAscent.good_of_no_strict_ascent
    (RepairMove h2N) RelationOrientable closurePotential hascent A hmax

end Rank4GcdTwoRepair
end HigherRankKUM
