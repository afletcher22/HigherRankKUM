import HigherRankKUM.BlockerClosure
import HigherRankKUM.Rank4.GcdTwoDeletion

namespace HigherRankKUM
namespace Rank4BlockerDangerousBridge

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- A saturated rank-three set spanning an omitted element forces a dangerous
hyperplane.

More precisely, in a strict rank-four `4k+2` instance, suppose `X` has
rank three and exactly `3k` elements, while a ground element `e ∉ X` lies
in `cl(X)`.  Then `cl(X)` has exactly one more element than `X` can have:
strict density gives the upper bound `3k+1`, while `e` gives the strict
lower bound.  Hence `cl(X)` is a dangerous hyperplane. -/
theorem dangerousHyperplane_closure_of_rankThree_saturated_spans
    {M : Matroid α} {k : ℕ} {X : Set α} {e : α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hXsub : X ⊆ M.E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hXcard : X.ncard = 3 * k)
    (heE : e ∈ M.E)
    (heX : e ∉ X)
    (hecl : e ∈ M.closure X) :
    Rank4GcdTwoDeletion.DangerousHyperplane M k (M.closure X) := by
  have hXfin : X.Finite := hE.subset hXsub
  have hclSub : M.closure X ⊆ M.E :=
    M.closure_subset_ground X
  have hclFin : (M.closure X).Finite :=
    hE.subset hclSub
  have hclRank : M.eRk (M.closure X) = (3 : ℕ∞) := by
    rw [M.eRk_closure_eq, hXrank]
  have hclProper : M.closure X ≠ M.E := by
    intro hEq
    have hr := hclRank
    rw [hEq, M.eRk_ground, hRank] at hr
    norm_num at hr
  have hclNonempty : (M.closure X).Nonempty :=
    ⟨e, hecl⟩
  have hs :=
    hStrict (M.closure X) hclSub hclNonempty hclProper
  rw [← hclFin.cast_ncard_eq, hclRank] at hs
  have hsNat :
      4 * (M.closure X).ncard < (4 * k + 2) * 3 := by
    exact_mod_cast hs
  have hupper : (M.closure X).ncard ≤ 3 * k + 1 := by
    omega
  have hne : X ≠ M.closure X := by
    intro hEq
    apply heX
    rw [hEq]
    exact hecl
  have hss : X ⊂ M.closure X :=
    (M.subset_closure X hXsub).ssubset_of_ne hne
  have hlower : 3 * k + 1 ≤ (M.closure X).ncard := by
    have hlt : X.ncard < (M.closure X).ncard :=
      Set.ncard_lt_ncard hss hclFin
    rw [hXcard] at hlt
    omega
  have hclCard : (M.closure X).ncard = 3 * k + 1 := by
    omega
  have hclEncard :
      (M.closure X).encard = ((3 * k + 1 : ℕ) : ℕ∞) := by
    rw [← hclFin.cast_ncard_eq, hclCard]
  exact ⟨M.isFlat_closure X, hclRank, hclEncard⟩

/-- Contrapositive form useful in the t=0 program: if there are no dangerous
hyperplanes, then no rank-three set of size `3k` can span a ground element
outside it. -/
theorem not_mem_closure_rankThree_saturated_of_no_dangerous
    {M : Matroid α} {k : ℕ} {X : Set α} {e : α}
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hNoDangerous :
      ∀ H : Set α, ¬ Rank4GcdTwoDeletion.DangerousHyperplane M k H)
    (hXsub : X ⊆ M.E)
    (hXrank : M.eRk X = (3 : ℕ∞))
    (hXcard : X.ncard = 3 * k)
    (heE : e ∈ M.E)
    (heX : e ∉ X) :
    e ∉ M.closure X := by
  intro hecl
  exact hNoDangerous (M.closure X)
    (dangerousHyperplane_closure_of_rankThree_saturated_spans
      hE hRank hStrict hXsub hXrank hXcard heE heX hecl)

end

end Rank4BlockerDangerousBridge
end HigherRankKUM
