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

/-- In the intended odd-`N` gcd-two regime, a non-orientable admissible state
has a forced bijection relation at every local index.  This is the local part
of the Sprint 2 obstruction theorem, packaged for the repair-dynamics layer. -/
theorem all_local_relations_bijective_of_not_relationOrientable
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (h2N : 2 < N) (hcop : Nat.gcd N 2 = 1)
    (hnot : ¬ RelationOrientable A) :
    ∀ i : Fin N,
      BinaryRelationCycle.BijectionRelation
        (A.localRelation (by omega) i) := by
  have hforced :=
    (PairCycleObstruction.admissible_pair_cycle_not_orientable_iff
      A (by omega) h2N hcop).1 (by
        simpa [RelationOrientable] using hnot)
  exact hforced.1

/-- Conversely, in the odd-`N` gcd-two regime a single local relation with
Boolean slack makes the whole fixed pair cycle relation-orientable.  This is
the formal escape test used by the refined Sprint 4 dynamics. -/
theorem relationOrientable_of_local_slack
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (h2N : 2 < N) (hcop : Nat.gcd N 2 = 1)
    (hslack : ∃ i : Fin N,
      ¬ BinaryRelationCycle.BijectionRelation
        (A.localRelation (by omega) i)) :
    RelationOrientable A := by
  simpa [RelationOrientable] using
    PairCycleObstruction.admissible_pair_cycle_orientable_of_local_slack
      A (by omega) h2N hcop hslack

/-- Strong sufficient reduction: if every non-orientable state has a strictly
closure-potential-increasing repair, then every state reaches a
relation-orientable state.  This theorem remains useful, but Sprint 4 finite
search found that its hypothesis is too strong to expect universally. -/
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

/-- Local-maximum version of the strict-ascent reduction. -/
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

/-- Refined Sprint 4 reduction.  A non-orientable state is allowed either to
escape directly to a relation-orientable repaired state, or to continue by a
strictly closure-potential-increasing repair.  Since `closurePotential ≤ 4N`,
this disjunction still guarantees finite reachability of an orientable state.

Unlike pure strict ascent, this hypothesis is compatible with closure-potential
plateaus that already have an edge into the orientable region. -/
theorem exists_reachable_relationOrientable_of_escape_or_strict_closure_ascent
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (h2N : 2 < N)
    (hstep : ∀ A : AdmissiblePairCycle.Data M N 2 hN,
      ¬ RelationOrientable A →
      (∃ B : AdmissiblePairCycle.Data M N 2 hN,
        RepairMove h2N A B ∧ RelationOrientable B) ∨
      (∃ B : AdmissiblePairCycle.Data M N 2 hN,
        RepairMove h2N A B ∧ closurePotential A < closurePotential B)) :
    ∀ A : AdmissiblePairCycle.Data M N 2 hN,
      ∃ B : AdmissiblePairCycle.Data M N 2 hN,
        Relation.ReflTransGen (RepairMove h2N) A B ∧ RelationOrientable B := by
  exact PotentialAscent.exists_reachable_good_of_bounded_escape_or_strict_ascent
    (RepairMove h2N) RelationOrientable closurePotential (4 * N)
    (fun A => closurePotential_le_four_mul A) hstep

/-- At a closure-potential local maximum, the refined step hypothesis reduces
to an immediate escape statement: the state is already relation-orientable or
has a one-step repair to a relation-orientable state. -/
theorem relationOrientable_or_exists_orientable_repair_of_no_closure_ascent
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (h2N : 2 < N)
    (hstep : ∀ A : AdmissiblePairCycle.Data M N 2 hN,
      ¬ RelationOrientable A →
      (∃ B : AdmissiblePairCycle.Data M N 2 hN,
        RepairMove h2N A B ∧ RelationOrientable B) ∨
      (∃ B : AdmissiblePairCycle.Data M N 2 hN,
        RepairMove h2N A B ∧ closurePotential A < closurePotential B))
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (hmax : ∀ B, RepairMove h2N A B → closurePotential B ≤ closurePotential A) :
    RelationOrientable A ∨
      ∃ B : AdmissiblePairCycle.Data M N 2 hN,
        RepairMove h2N A B ∧ RelationOrientable B := by
  exact PotentialAscent.good_or_exists_good_move_of_no_strict_ascent
    (RepairMove h2N) RelationOrientable closurePotential hstep A hmax

end Rank4GcdTwoRepair
end HigherRankKUM
