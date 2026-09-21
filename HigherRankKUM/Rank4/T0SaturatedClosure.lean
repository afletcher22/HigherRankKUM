import HigherRankKUM.Rank4.T0SaturatedCap
import HigherRankKUM.Rank4.SaturatedFlatRankThree

namespace HigherRankKUM
namespace Rank4T0SaturatedClosure

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- In the actual rank-four `4k+2` ground, a t=0 saturated deletion blocker
has no hidden closure points.

If `X ⊆ E = M.E \ {e}` has rank three, size `3k-1`, and spans the
omitted element `e`, then

`cl_M(X) = X ∪ {e}`.

Any further deletion-ground point `y` in the same closure would make
`X ∪ {y}` a rank-three `3k`-element deletion set still spanning `e`,
contradicting the certified no-dangerous `3k-1` cap. -/
theorem closure_eq_insert_omitted_of_saturated
    {M : Matroid α} {k : ℕ} {E X : Set α} {e : α}
    (hk : 0 < k)
    (hGroundFin : M.E.Finite)
    (hGroundCard : M.E.ncard = 4 * k + 2)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hEfin : E.Finite)
    (hEcard : E.ncard = 4 * k + 1)
    (hEsub : E ⊆ M.E)
    (heE : e ∈ M.E)
    (heNotE : e ∉ E)
    (hXsub : X ⊆ E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hecl : e ∈ M.closure X)
    (hXcard : X.ncard = 3 * k - 1)
    (σ : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    M.closure X = insert e X := by
  have hXfin : X.Finite := hEfin.subset hXsub
  have hXground : X ⊆ M.E := hXsub.trans hEsub
  have heNotX : e ∉ X := fun heX => heNotE (hXsub heX)
  have hInsertEsub : insert e E ⊆ M.E := by
    exact Set.insert_subset heE hEsub
  have hInsertEcard : (insert e E).ncard = 4 * k + 2 := by
    rw [Set.ncard_insert_of_notMem heNotE hEfin, hEcard]
  have hGroundEq : insert e E = M.E := by
    apply Set.eq_of_subset_of_ncard_le hInsertEsub
    rw [hInsertEcard, hGroundCard]
  apply Set.Subset.antisymm
  · intro y hy
    have hyGround : y ∈ M.E := M.closure_subset_ground X hy
    have hyInsertE : y ∈ insert e E := by
      rw [hGroundEq]
      exact hyGround
    rcases hyInsertE with rfl | hyE
    · exact Set.mem_insert e X
    by_cases hyX : y ∈ X
    · exact Set.mem_insert_of_mem e hyX
    · let Y : Set α := insert y X
      have hYsubE : Y ⊆ E := by
        dsimp [Y]
        exact Set.insert_subset hyE hXsub
      have hYfin : Y.Finite := hEfin.subset hYsubE
      have hYcard : Y.ncard = 3 * k := by
        dsimp [Y]
        rw [Set.ncard_insert_of_notMem hyX hXfin, hXcard]
        omega
      have hYsubCl : Y ⊆ M.closure X := by
        dsimp [Y]
        refine Set.insert_subset hy ?_
        exact M.subset_closure X hXground
      have hYrankLe : M.eRk Y ≤ (3 : ℕ∞) := by
        calc
          M.eRk Y ≤ M.eRk (M.closure X) := M.eRk_mono hYsubCl
          _ = M.eRk X := M.eRk_closure_eq X
          _ = (3 : ℕ∞) := hXrank
      have hXsubY : X ⊆ Y := by
        dsimp [Y]
        exact Set.subset_insert y X
      have hYrankGe : (3 : ℕ∞) ≤ M.eRk Y := by
        rw [← hXrank]
        exact M.eRk_mono hXsubY
      have hYrank : M.eRk Y = (3 : ℕ∞) :=
        le_antisymm hYrankLe hYrankGe
      have heclY : e ∈ M.closure Y := by
        exact M.closure_subset_closure hXsubY hecl
      have hcap :=
        Rank4T0SaturatedCap.rankThree_spanning_ncard_le_three_mul_sub_one_of_no_dangerous
          hGroundFin hRank hStrict hNoDangerous
          hEfin hEcard hEsub heE heNotE
          hYsubE hYrank heclY σ hCBO
      rw [hYcard] at hcap
      omega
  · exact Set.insert_subset hecl (M.subset_closure X hXground)

/-- A saturated deletion blocker therefore closes to exactly `3k` ambient
elements and remains rank three. -/
theorem saturated_closure_rank_card
    {M : Matroid α} {k : ℕ} {E X : Set α} {e : α}
    (hk : 0 < k)
    (hGroundFin : M.E.Finite)
    (hGroundCard : M.E.ncard = 4 * k + 2)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hEfin : E.Finite)
    (hEcard : E.ncard = 4 * k + 1)
    (hEsub : E ⊆ M.E)
    (heE : e ∈ M.E)
    (heNotE : e ∉ E)
    (hXsub : X ⊆ E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hecl : e ∈ M.closure X)
    (hXcard : X.ncard = 3 * k - 1)
    (σ : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    M.eRk (M.closure X) = (3 : ℕ∞) ∧
      (M.closure X).ncard = 3 * k := by
  have hcl :=
    closure_eq_insert_omitted_of_saturated
      hk hGroundFin hGroundCard hRank hStrict hNoDangerous
      hEfin hEcard hEsub heE heNotE hXsub hXrank hecl hXcard
      σ hCBO
  have hXfin : X.Finite := hEfin.subset hXsub
  have heNotX : e ∉ X := fun heX => heNotE (hXsub heX)
  constructor
  · simpa using hXrank
  · rw [hcl, Set.ncard_insert_of_notMem heNotX hXfin, hXcard]
    omega

/-- Constructive saturation bridge.

Every t=0 saturated deletion blocker closes to a `3k`-element rank-three
restriction, and that restriction has a cyclic basis ordering by the frozen
rank-three KUM theorem. -/
theorem exists_rankThree_cbo_of_saturated_deletion_blocker
    {M : Matroid α} {k : ℕ} {E X : Set α} {e : α}
    (hk : 0 < k)
    (hGroundFin : M.E.Finite)
    (hGroundCard : M.E.ncard = 4 * k + 2)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hEfin : E.Finite)
    (hEcard : E.ncard = 4 * k + 1)
    (hEsub : E ⊆ M.E)
    (heE : e ∈ M.E)
    (heNotE : e ∉ E)
    (hXsub : X ⊆ E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hecl : e ∈ M.closure X)
    (hXcard : X.ncard = 3 * k - 1)
    (σ : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    ∃ order : Fin (3 * k) ≃ (M ↾ M.closure X).E,
      CyclicBasisOrder (M ↾ M.closure X) 3 (by omega) order := by
  obtain ⟨hClRank, hClCard⟩ :=
    saturated_closure_rank_card
      hk hGroundFin hGroundCard hRank hStrict hNoDangerous
      hEfin hEcard hEsub heE heNotE hXsub hXrank hecl hXcard
      σ hCBO
  exact
    Rank4SaturatedFlatRankThree.exists_cyclicBasisOrder_restrict_of_rankThree_ncard_three_mul
      hk hGroundFin hRank hStrict
      (M.closure_subset_ground X) hClRank hClCard

end

end Rank4T0SaturatedClosure
end HigherRankKUM
