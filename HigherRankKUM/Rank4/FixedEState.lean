import HigherRankKUM.Rank4.BlockerCycle
import HigherRankKUM.Rank4.FourBlockPerm
import Mathlib.Logic.Relation

namespace HigherRankKUM
namespace Rank4FixedEState

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- A fixed-omitted-element rank-four CBO state.

The order enumerates exactly `M.E \ {e}`, and its consecutive four-windows
are bases of the original matroid `M`.  This is the convenient form of a
rank-preserving deletion CBO for blocker/insertion arguments. -/
structure State
    (M : Matroid α) (e : α) (n : ℕ) (hn : 0 < n) where
  order : Fin n ≃ M.E \ ({e} : Set α)
  cbo : CyclicBasisOrder M 4 hn order

namespace State

/-- A state is blocker-favorable when its blocker word has a cyclic run of at
least four consecutive zeroes.

This is the exact blocker-side success condition.  The separate insertion
adapter will later identify it with existence of an insertion gap. -/
def Favorable
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    (S : State M e n hn) : Prop :=
  ∃ i : Fin n, ∀ q : Fin 4,
    ¬ Rank4BlockerCycle.blockerAt M hn S.order e
      (cyclicIndex n hn i q.val)

/-- Explicit four-conjunction form of blocker favorability. -/
theorem favorable_iff_four_nonblockers
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    (S : State M e n hn) :
    S.Favorable ↔
      ∃ i : Fin n,
        ¬ Rank4BlockerCycle.blockerAt M hn S.order e i ∧
        ¬ Rank4BlockerCycle.blockerAt M hn S.order e
          (cyclicIndex n hn i 1) ∧
        ¬ Rank4BlockerCycle.blockerAt M hn S.order e
          (cyclicIndex n hn i 2) ∧
        ¬ Rank4BlockerCycle.blockerAt M hn S.order e
          (cyclicIndex n hn i 3) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_, ?_, ?_, ?_⟩
    · simpa [cyclicIndex_zero] using hi (0 : Fin 4)
    · simpa using hi (1 : Fin 4)
    · simpa using hi (2 : Fin 4)
    · simpa using hi (3 : Fin 4)
  · rintro ⟨i, h0, h1, h2, h3⟩
    refine ⟨i, ?_⟩
    intro q
    fin_cases q
    · simpa [cyclicIndex_zero] using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3

/-- Four blockers cannot occur consecutively in any fixed-e CBO state when
the omitted element is a nonloop. -/
theorem no_four_consecutive_blockers
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    (S : State M e n hn)
    (h6n : 6 ≤ n) (he : M.IsNonloop e) (i : Fin n) :
    ¬ (Rank4BlockerCycle.blockerAt M hn S.order e i ∧
       Rank4BlockerCycle.blockerAt M hn S.order e
         (cyclicIndex n hn i 1) ∧
       Rank4BlockerCycle.blockerAt M hn S.order e
         (cyclicIndex n hn i 2) ∧
       Rank4BlockerCycle.blockerAt M hn S.order e
         (cyclicIndex n hn i 3)) := by
  exact Rank4BlockerCycle.no_four_consecutive_blockers
    hn h6n S.order e he S.cbo i

end State

/-- One valid fixed-e graph edge: the two states differ by a local
CBO-preserving permutation of four consecutive positions. -/
def FourBlockStep
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    (h4n : 4 ≤ n)
    (S T : State M e n hn) : Prop :=
  Rank4FourBlockMove.FourBlockMove hn h4n S.order T.order

theorem fourBlockStep_symm
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    {h4n : 4 ≤ n}
    {S T : State M e n hn}
    (h : FourBlockStep h4n S T) :
    FourBlockStep h4n T S := by
  exact Rank4FourBlockMove.FourBlockMove.symm h

/-- Reachability inside the fixed-e four-block component. -/
def Reachable
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    (h4n : 4 ≤ n)
    (S T : State M e n hn) : Prop :=
  Relation.ReflTransGen (FourBlockStep h4n) S T

theorem reachable_refl
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    (h4n : 4 ≤ n) (S : State M e n hn) :
    Reachable h4n S S := by
  exact Relation.ReflTransGen.refl

theorem reachable_trans
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    {h4n : 4 ≤ n}
    {S T U : State M e n hn}
    (hST : Reachable h4n S T)
    (hTU : Reachable h4n T U) :
    Reachable h4n S U := by
  exact hST.trans hTU

theorem reachable_symm
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    {h4n : 4 ≤ n}
    {S T : State M e n hn}
    (h : Reachable h4n S T) :
    Reachable h4n T S := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hST hTU ih =>
      exact ih.head (fourBlockStep_symm hTU)

/-- The fixed-e component of a state contains a blocker-favorable state. -/
def ComponentHasFavorable
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    (h4n : 4 ≤ n)
    (S : State M e n hn) : Prop :=
  ∃ T : State M e n hn, Reachable h4n S T ∧ T.Favorable

/-- Exact fixed-e component property suggested by the post-t>0 experiments.

This is a definition, not a theorem: every four-block component contains a
blocker-favorable state. -/
def EveryComponentHasFavorable
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    (h4n : 4 ≤ n) : Prop :=
  ∀ S : State M e n hn, ComponentHasFavorable h4n S

/-- Component favorability is constant across a fixed-e component. -/
theorem componentHasFavorable_of_reachable
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    {h4n : 4 ≤ n}
    {S T : State M e n hn}
    (hST : Reachable h4n S T)
    (hT : ComponentHasFavorable h4n T) :
    ComponentHasFavorable h4n S := by
  rcases hT with ⟨U, hTU, hFav⟩
  exact ⟨U, reachable_trans hST hTU, hFav⟩

theorem componentHasFavorable_iff_of_reachable
    {M : Matroid α} {e : α} {n : ℕ} {hn : 0 < n}
    {h4n : 4 ≤ n}
    {S T : State M e n hn}
    (hST : Reachable h4n S T) :
    ComponentHasFavorable h4n S ↔ ComponentHasFavorable h4n T := by
  constructor
  · intro hS
    exact componentHasFavorable_of_reachable (reachable_symm hST) hS
  · intro hT
    exact componentHasFavorable_of_reachable hST hT

end

end Rank4FixedEState
end HigherRankKUM
