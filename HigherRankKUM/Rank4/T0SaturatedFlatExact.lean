import HigherRankKUM.Rank4.T0SaturatedCap
import HigherRankKUM.Rank4.SaturatedFlatRankThree

namespace HigherRankKUM
namespace Rank4T0SaturatedFlatExact

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- In an actual one-element deletion state, a t=0-saturated rank-three
blocker set has exact closure obtained by adjoining the omitted element.

If X has size 3k-1, rank three, and spans e, then any further deletion
element y in cl(X) would make insert y X a 3k-element rank-three set still
spanning e, contradicting the certified no-dangerous 3k-1 cap. -/
theorem closure_eq_insert_omitted_of_saturated
    {M : Matroid α} {k : ℕ} {E X : Set α} {e : α}
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hEfin : E.Finite)
    (hEcard : E.ncard = 4 * k + 1)
    (hEeq : E = M.E \ {e})
    (heE : e ∈ M.E)
    (hXsub : X ⊆ E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hecl : e ∈ M.closure X)
    (hXcard : X.ncard = 3 * k - 1)
    (σ : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    M.closure X = insert e X := by
  have hEsub : E ⊆ M.E := by
    rw [hEeq]
    exact Set.sdiff_subset
  have heNotE : e ∉ E := by
    rw [hEeq]
    simp
  have hXground : X ⊆ M.E := hXsub.trans hEsub
  have hXfin : X.Finite := hEfin.subset hXsub
  apply Set.Subset.antisymm
  · intro y hycl
    by_cases hye : y = e
    · subst y
      simp
    by_cases hyX : y ∈ X
    · exact Set.mem_insert_iff.mpr (Or.inr hyX)
    have hyGround : y ∈ M.E :=
      M.mem_ground_of_mem_closure hycl
    have hyE : y ∈ E := by
      rw [hEeq]
      exact ⟨hyGround, by simpa [hye]⟩
    let Y : Set α := insert y X
    have hYsub : Y ⊆ E := by
      dsimp [Y]
      exact Set.insert_subset hyE hXsub
    have hYrank : M.eRk Y = (3 : ℕ∞) := by
      dsimp [Y]
      have hclEq :=
        M.closure_insert_eq_of_mem_closure hycl
      calc
        M.eRk (insert y X)
            = M.eRk (M.closure (insert y X)) := by
                rw [M.eRk_closure_eq]
        _ = M.eRk (M.closure X) := by rw [hclEq]
        _ = M.eRk X := M.eRk_closure_eq
        _ = (3 : ℕ∞) := hXrank
    have heclY : e ∈ M.closure Y := by
      exact M.closure_mono (Set.subset_insert y X) hecl
    have hYcard : Y.ncard = 3 * k := by
      dsimp [Y]
      rw [Set.ncard_insert_of_notMem hyX hXfin, hXcard]
      omega
    have hcap :=
      Rank4T0SaturatedCap.rankThree_spanning_ncard_le_three_mul_sub_one_of_no_dangerous
        hGroundFin hRank hStrict hNoDangerous
        hEfin hEcard hEsub heE heNotE
        hYsub hYrank heclY σ hCBO
    rw [hYcard] at hcap
    omega
  · intro y hy
    rw [Set.mem_insert_iff] at hy
    rcases hy with rfl | hyX
    · exact hecl
    · exact M.subset_closure X hXground hyX

/-- Consequently the saturated closure has exactly 3k elements. -/
theorem closure_ncard_eq_three_mul_of_saturated
    {M : Matroid α} {k : ℕ} {E X : Set α} {e : α}
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hEfin : E.Finite)
    (hEcard : E.ncard = 4 * k + 1)
    (hEeq : E = M.E \ {e})
    (heE : e ∈ M.E)
    (hXsub : X ⊆ E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hecl : e ∈ M.closure X)
    (hXcard : X.ncard = 3 * k - 1)
    (σ : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    (M.closure X).ncard = 3 * k := by
  have hcl :=
    closure_eq_insert_omitted_of_saturated
      hGroundFin hRank hStrict hNoDangerous hEfin hEcard hEeq heE
      hXsub hXrank hecl hXcard σ hCBO
  rw [hcl]
  have heX : e ∉ X := by
    intro hex
    have : e ∈ E := hXsub hex
    rw [hEeq] at this
    exact this.2 (by simp)
  have hXfin : X.Finite := hEfin.subset hXsub
  rw [Set.ncard_insert_of_notMem heX hXfin, hXcard]
  omega


/-- A t=0-saturated blocker flat is itself a solved divisible rank-three
instance.

Under the actual deletion identity, its closure is exactly X ∪ {e}, has
cardinality 3k and rank three, and therefore inherits uniform density from
strict rank-four density.  The frozen Rank3KUM theorem supplies a cyclic
basis order of the restriction. -/
theorem exists_cyclicBasisOrder_saturated_closure
    {M : Matroid α} {k : ℕ} {E X : Set α} {e : α}
    (hk : 0 < k)
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hEfin : E.Finite)
    (hEcard : E.ncard = 4 * k + 1)
    (hEeq : E = M.E \ {e})
    (heE : e ∈ M.E)
    (hXsub : X ⊆ E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hecl : e ∈ M.closure X)
    (hXcard : X.ncard = 3 * k - 1)
    (σ : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    ∃ order : Fin (3 * k) ≃ (M ↾ M.closure X).E,
      CyclicBasisOrder (M ↾ M.closure X) 3 (by omega) order := by
  have hclCard :
      (M.closure X).ncard = 3 * k :=
    closure_ncard_eq_three_mul_of_saturated
      hGroundFin hRank hStrict hNoDangerous
      hEfin hEcard hEeq heE hXsub hXrank hecl hXcard σ hCBO
  have hclRank :
      M.eRk (M.closure X) = (3 : ℕ∞) := by
    rw [M.eRk_closure_eq, hXrank]
  exact
    Rank4SaturatedFlatRankThree.exists_cyclicBasisOrder_restrict_of_rankThree_ncard_three_mul
      hk hGroundFin hRank hStrict
      (M.closure_subset_ground X) hclRank hclCard

end

end Rank4T0SaturatedFlatExact
end HigherRankKUM
