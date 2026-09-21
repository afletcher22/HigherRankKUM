import HigherRankKUM.Rank4.BlockerRuns
import HigherRankKUM.Rank4.CyclicFlatCapacity
import HigherRankKUM.Rank4.FourBlockPerm

namespace HigherRankKUM
namespace Rank4FixedEState

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- The blocker positions of a cyclic deletion order with respect to a fixed
omitted element `e`. -/
def blockerPositions
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (e : α) :
    Set (Fin n) :=
  {i | Rank4BlockerCycle.blockerAt M hn σ e i}

/-- The complementary set of nonblocker positions. -/
def nonblockerPositions
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (e : α) :
    Set (Fin n) :=
  {i | ¬ Rank4BlockerCycle.blockerAt M hn σ e i}

/-- A favorable start is a cyclic run of four consecutive nonblocker
positions.  By the exact blocker criterion from the computational research,
this is the local condition corresponding to an insertion gap. -/
def FavorableAt
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (e : α) (i : Fin n) : Prop :=
  ∀ q : Fin 4,
    ¬ Rank4BlockerCycle.blockerAt M hn σ e
      (cyclicIndex n hn i q.val)

/-- A fixed omitted element is favorable for the cyclic order when some
length-four run of blocker positions is entirely zero. -/
def Favorable
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (e : α) : Prop :=
  ∃ i : Fin n, FavorableAt M hn σ e i

/-- A CBO-preserving four-block move between two cyclic enumerations of the
same deletion ground. -/
def FourBlockCBOStep
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ τ : Fin n ≃ E) : Prop :=
  CyclicBasisOrder M 4 hn σ ∧
  CyclicBasisOrder M 4 hn τ ∧
  Rank4FourBlockMove.FourBlockMove hn h4n σ τ

theorem FourBlockCBOStep.symm
    {M : Matroid α} {E : Set α} {n : ℕ}
    {hn : 0 < n} {h4n : 4 ≤ n}
    {σ τ : Fin n ≃ E}
    (h : FourBlockCBOStep M hn h4n σ τ) :
    FourBlockCBOStep M hn h4n τ σ := by
  exact ⟨h.2.1, h.1, h.2.2.symm⟩

/-- Fixed-e reachability under CBO-preserving four-block moves. -/
def FourBlockReachable
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (σ τ : Fin n ≃ E) : Prop :=
  Relation.ReflTransGen (FourBlockCBOStep M hn h4n) σ τ

/-- The exact fixed-e component property suggested by the post-t>0
experiments: every CBO state can reach a favorable state without changing the
omitted element. -/
def FixedEFavorableComponentProperty
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n) (e : α) : Prop :=
  ∀ σ : Fin n ≃ E,
    CyclicBasisOrder M 4 hn σ →
      ∃ τ : Fin n ≃ E,
        FourBlockReachable M hn h4n σ τ ∧
        Favorable M hn τ e

/-- If a state is not favorable, then every four consecutive blocker
positions contain at least one blocker. -/
theorem blocker_hit_every_four_of_not_favorable
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (e : α)
    (hbad : ¬ Favorable M hn σ e) :
    ∀ i : Fin n,
      Rank4BlockerCycle.blockerAt M hn σ e i ∨
      Rank4BlockerCycle.blockerAt M hn σ e
        (cyclicIndex n hn i 1) ∨
      Rank4BlockerCycle.blockerAt M hn σ e
        (cyclicIndex n hn i 2) ∨
      Rank4BlockerCycle.blockerAt M hn σ e
        (cyclicIndex n hn i 3) := by
  intro i
  by_contra hnone
  push_neg at hnone
  apply hbad
  refine ⟨i, ?_⟩
  intro q
  fin_cases q
  · simpa [cyclicIndex_zero] using hnone.1
  · simpa using hnone.2.1
  · simpa using hnone.2.2.1
  · simpa using hnone.2.2.2

/-- On a bad `4k+1` deletion order, at least `k+1` cyclic triple starts are
blockers.  This is purely the cyclic hitting-set consequence of having no
four-zero run. -/
theorem blocker_ncard_ge_k_add_one_of_not_favorable
    {M : Matroid α} {E : Set α} {k : ℕ}
    (σ : Fin (4 * k + 1) ≃ E) (e : α)
    (hbad : ¬ Favorable M (by omega) σ e) :
    k + 1 ≤
      (blockerPositions M (by omega) σ e).ncard := by
  apply Rank4CyclicFlatCapacity.ncard_good_ge_k_add_one_of_hits_every_four
  exact blocker_hit_every_four_of_not_favorable
    (M := M) (hn := by omega) σ e hbad

/-- Along a rank-four CBO, nonblockers also hit every four consecutive blocker
positions, because four consecutive blockers are impossible. -/
theorem nonblocker_hit_every_four_of_cbo
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h6n : 6 ≤ n)
    (σ : Fin n ≃ E) (e : α)
    (he : M.IsNonloop e)
    (hCBO : CyclicBasisOrder M 4 hn σ) :
    ∀ i : Fin n,
      ¬ Rank4BlockerCycle.blockerAt M hn σ e i ∨
      ¬ Rank4BlockerCycle.blockerAt M hn σ e
        (cyclicIndex n hn i 1) ∨
      ¬ Rank4BlockerCycle.blockerAt M hn σ e
        (cyclicIndex n hn i 2) ∨
      ¬ Rank4BlockerCycle.blockerAt M hn σ e
        (cyclicIndex n hn i 3) := by
  intro i
  by_contra hall
  push_neg at hall
  exact
    (Rank4BlockerCycle.no_four_consecutive_blockers
      hn h6n σ e he hCBO i) hall

/-- On a `4k+1` rank-four CBO with `k ≥ 2`, at least `k+1` triple starts
are nonblockers. -/
theorem nonblocker_ncard_ge_k_add_one_of_cbo
    {M : Matroid α} {E : Set α} {k : ℕ}
    (hk : 2 ≤ k)
    (σ : Fin (4 * k + 1) ≃ E) (e : α)
    (he : M.IsNonloop e)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    k + 1 ≤
      (nonblockerPositions M (by omega) σ e).ncard := by
  apply Rank4CyclicFlatCapacity.ncard_good_ge_k_add_one_of_hits_every_four
  exact nonblocker_hit_every_four_of_cbo
    (M := M) (hn := by omega) (h6n := by omega) σ e he hCBO

end

end Rank4FixedEState
end HigherRankKUM
