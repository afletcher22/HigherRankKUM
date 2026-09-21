import HigherRankKUM.Rank4.BlockerDangerousBridge
import HigherRankKUM.Rank4.CyclicFlatCapacity

namespace HigherRankKUM
namespace Rank4T0SaturatedCap

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- Exact complement size for a t=0-saturated rank-three set.

Inside a deletion ground of size `4k+1`, a set of size `3k-1` leaves
exactly `k+2` deletion elements outside. -/
theorem saturated_rankThree_complement_ncard_eq_k_add_two
    {E X : Set α} {k : ℕ}
    (hk : 1 ≤ k)
    (hEfin : E.Finite)
    (hEcard : E.ncard = 4 * k + 1)
    (hXsub : X ⊆ E)
    (hXcard : X.ncard = 3 * k - 1) :
    (E \ X).ncard = k + 2 := by
  have hdiff : (E \ X).ncard = E.ncard - X.ncard :=
    Set.ncard_sdiff' hXsub hEfin
  rw [hdiff, hEcard, hXcard]
  omega

/-- Saturated rank-three complement package.

A size-`3k-1` rank-at-most-three set in a rank-four `4k+1` CBO has a
`k+2`-element complement, and that complement hits every four consecutive
positions.  This is the combinatorial interface suggested by the hard-state
saturation experiments. -/
theorem saturated_rankThree_complement_package
    {M : Matroid α} {E X : Set α} {k : ℕ}
    (hk : 1 ≤ k)
    (hEfin : E.Finite)
    (hEcard : E.ncard = 4 * k + 1)
    (hXsub : X ⊆ E)
    (hRank : M.eRank = (4 : ℕ∞))
    (hXrank : M.eRk X ≤ (3 : ℕ∞))
    (hXcard : X.ncard = 3 * k - 1)
    (σ : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    (E \ X).ncard = k + 2 ∧
    ∀ i : Fin (4 * k + 1),
      (σ i : α) ∈ E \ X ∨
      (σ (cyclicIndex (4 * k + 1) (by omega) i 1) : α) ∈ E \ X ∨
      (σ (cyclicIndex (4 * k + 1) (by omega) i 2) : α) ∈ E \ X ∨
      (σ (cyclicIndex (4 * k + 1) (by omega) i 3) : α) ∈ E \ X := by
  refine ⟨
    saturated_rankThree_complement_ncard_eq_k_add_two
      hk hEfin hEcard hXsub hXcard,
    ?_⟩
  intro i
  have hhit :=
    Rank4CyclicFlatCapacity.rankThree_complement_hits_every_four_of_cyclicBasisOrder
      (M := M) (H := X) (hn := by omega)
      hRank hXrank σ hCBO i
  rcases hhit with h0 | h1 | h2 | h3
  · exact Or.inl ⟨(σ i).property, h0⟩
  · exact Or.inr (Or.inl
      ⟨(σ (cyclicIndex (4 * k + 1) (by omega) i 1)).property, h1⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨(σ (cyclicIndex (4 * k + 1) (by omega) i 2)).property, h2⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨(σ (cyclicIndex (4 * k + 1) (by omega) i 3)).property, h3⟩))

/-- In the no-dangerous `4k+2` branch, a rank-three set in a `4k+1`
deletion CBO that spans the omitted element has at most `3k-1` elements.

The ordinary cyclic-basis packing bound gives `|X| ≤ 3k`.  Equality would
make `X` a saturated rank-three blocker set, and the
blocker-dangerous bridge would then force `cl(X)` to be a dangerous
hyperplane. -/
theorem rankThree_spanning_ncard_le_three_mul_sub_one_of_no_dangerous
    {M : Matroid α} {k : ℕ} {E X : Set α} {e : α}
    (hGroundFin : M.E.Finite)
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
    (σ : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    X.ncard ≤ 3 * k - 1 := by
  have hcap : X.ncard ≤ 3 * k :=
    Rank4CyclicFlatCapacity.rankThree_ncard_le_three_mul_of_cyclicBasisOrder
      hEfin hEcard hXsub hRank hXrank.le σ hCBO
  by_contra hnot
  have hEq : X.ncard = 3 * k := by
    omega
  have hXground : X ⊆ M.E :=
    hXsub.trans hEsub
  have heX : e ∉ X := by
    intro hex
    exact heNotE (hXsub hex)
  exact
    (Rank4BlockerDangerousBridge.not_mem_closure_rankThree_saturated_of_no_dangerous
      hGroundFin hRank hStrict hNoDangerous
      hXground hXrank hEq heE heX) hecl

end

end Rank4T0SaturatedCap
end HigherRankKUM
