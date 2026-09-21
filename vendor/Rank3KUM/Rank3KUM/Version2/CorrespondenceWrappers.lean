import Rank3KUM.Interleave
import Rank3KUM.ContractInterleave

namespace Rank3KUM.Version2

open Set

variable {α : Type*}

/--
Paper v2, Lemma 5.1 in its paper-facing hypothesis form.  A distinct
independent pair inside a rank-two flat is automatically a basis of that
flat, after which the compiled lifting lemma applies.
-/
theorem isBase_insert_pair_of_indep_flat_rank3
    (M : Matroid α) {X : Set α}
    (hRank : M.eRank = 3)
    (hXflat : M.IsFlat X)
    (hXrank : M.eRk X = 2)
    {e f g : α}
    (heE : e ∈ M.E)
    (heX : e ∉ X)
    (hfX : f ∈ X)
    (hgX : g ∈ X)
    (hfg : f ≠ g)
    (hpair : M.Indep ({f, g} : Set α)) :
    M.IsBase ({e, f, g} : Set α) := by
  have hpairRank : M.eRk ({f, g} : Set α) = 2 := by
    rw [hpair.eRk_eq_encard, Set.encard_pair hfg]
  have hpairBasis : M.IsBasis ({f, g} : Set α) X := by
    apply hpair.isBasis_of_eRk_ge (Set.toFinite {f, g})
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hfX
      · exact hgX
    · rw [hXrank, hpairRank]
  exact
    Rank3KUM.isBase_insert_pair_of_isBasis_flat_rank3
      M hRank hXflat heE heX hfg hpairBasis

/--
Paper v2, Lemma 6.3 in its paper-facing hypothesis form.  In the rank-two
contraction a distinct independent pair is a base; looplessness and rank one
make the chosen point of `X` a singleton basis of `X`.
-/
theorem isBase_insert_pair_of_contract_indep_rank3
    (M : Matroid α) {X : Set α}
    (hRank : M.eRank = 3)
    (hContractRank : (Matroid.contract M X).eRank = 2)
    (hLoopless : M.Loopless)
    (hXsubset : X ⊆ M.E)
    (hXrank : M.eRk X = 1)
    {e f g : α}
    (heX : e ∈ X)
    (hfg : f ≠ g)
    (hpair : (Matroid.contract M X).Indep ({f, g} : Set α)) :
    M.IsBase ({e, f, g} : Set α) := by
  have heBasis : M.IsBasis ({e} : Set α) X :=
    Rank3KUM.isBasis_singleton_of_loopless_eRk_eq_one
      M hLoopless hXsubset hXrank heX
  have hpairBase :
      (Matroid.contract M X).IsBase ({f, g} : Set α) :=
    Rank3KUM.HalfWeave.pair_isBase_of_indep_of_eRank_eq_two
      (Matroid.contract M X) hContractRank hfg hpair
  exact
    Rank3KUM.isBase_insert_pair_of_contract_isBase_rank3
      M hRank hContractRank heBasis hpairBase

#print axioms Rank3KUM.Version2.isBase_insert_pair_of_indep_flat_rank3
#print axioms Rank3KUM.Version2.isBase_insert_pair_of_contract_indep_rank3

end Rank3KUM.Version2
