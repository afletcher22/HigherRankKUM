import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Combinatorics.Matroid.Minor.Contract

namespace HigherRankKUM

open Set

variable {α : Type*} {M : Matroid α} {B : Set α} {e f : α}

/-- For a basis `B`, replacing `f ∈ B` by an outside ground element `e`
produces a basis exactly when `f` lies in the fundamental circuit of `e`
with respect to `B`.

This is the fixed-basis replacement criterion needed in the six-block
rank-four repair analysis: several apparently different local basis tests are
single-element exchanges from the same middle basis. -/
theorem Matroid.IsBase.mem_fundCircuit_iff_exchange_isBase
    (hB : M.IsBase B) (heE : e ∈ M.E) (heB : e ∉ B) (hfB : f ∈ B) :
    f ∈ M.fundCircuit e B ↔ M.IsBase (insert e B \ {f}) := by
  rw [hB.indep.mem_fundCircuit_iff (by simpa [hB.closure_eq] using heE) heB]
  constructor
  · intro hI
    exact hB.exchange_isBase_of_indep' hfB heB hI
  · exact fun hBase => hBase.indep



/-- In a rank-two contraction witnessed by a two-element base, a distinct
outside ground element that fails to form a base with one endpoint is spanned
by that endpoint after contraction.  Undoing the contraction says that it is
spanned in the ambient matroid by the contracted set together with the
endpoint. -/
theorem Matroid.mem_closure_insert_of_contract_pair_not_isBase
    {C : Set α} {a a' c : α}
    (hA : (M.contract C).IsBase ({a, a'} : Set α))
    (haa' : a ≠ a') (hca : c ≠ a)
    (hcE : c ∈ (M.contract C).E)
    (hnot : ¬ (M.contract C).IsBase ({a, c} : Set α)) :
    c ∈ M.closure (insert a C) := by
  let N := M.contract C
  have haI : N.Indep ({a} : Set α) :=
    hA.indep.subset (by simp)
  have hpair_not_indep : ¬ N.Indep ({a, c} : Set α) := by
    intro hpair
    apply hnot
    apply hpair.isBase_of_eRk_ge
    rw [← hA.encard_eq_eRank, hpair.eRk_eq_encard]
    rw [Set.encard_pair haa', Set.encard_pair hca]
  have hccl : c ∈ N.closure ({a} : Set α) := by
    by_contra hcnot
    have hci : N.Indep (insert c ({a} : Set α)) :=
      (haI.insert_indep_iff_of_notMem (by simpa [hca])).2 ⟨hcE, hcnot⟩
    exact hpair_not_indep (by simpa [Set.pair_comm] using hci)
  change c ∈ (M.contract C).closure ({a} : Set α) at hccl
  rw [Matroid.contract_closure_eq] at hccl
  exact hccl.1


/-- A failed cross pair in a rank-two contraction becomes an ambient parallel
pair as soon as the outside element is already spanned by the original
two-element endpoint pair.

The hypotheses are intentionally local.  The union of the endpoint pair with
the contracted core is independent, the endpoint pair is a base after
contraction, and the outside element is a nonloop outside that independent
union. -/
theorem Matroid.isCircuit_pair_of_endpoint_closure_and_failed_contract_pair
    {C : Set α} {a a' c : α}
    (hI : M.Indep (({a, a'} : Set α) ∪ C))
    (hAC : Disjoint ({a, a'} : Set α) C)
    (haa' : a ≠ a')
    (hcI : c ∉ (({a, a'} : Set α) ∪ C))
    (hcNonloop : M.IsNonloop c)
    (hcEndpoint : c ∈ M.closure ({a, a'} : Set α))
    (hA : (M.contract C).IsBase ({a, a'} : Set α))
    (hnot : ¬ (M.contract C).IsBase ({a, c} : Set α)) :
    M.IsCircuit ({c, a} : Set α) := by
  have hcE : c ∈ (M.contract C).E := by
    rw [Matroid.contract_ground]
    exact ⟨hcNonloop.mem_ground, fun hcC => hcI (Or.inr hcC)⟩
  have hca : c ≠ a := by
    intro hca
    subst c
    exact hcI (Or.inl (by simp))
  have hcMiddle : c ∈ M.closure (insert a C) :=
    M.mem_closure_insert_of_contract_pair_not_isBase hA haa' hca hcE hnot
  have hpairI : ({a, a'} : Set α) ⊆ (({a, a'} : Set α) ∪ C) :=
    Set.subset_union_left
  have hmiddleI : insert a C ⊆ (({a, a'} : Set α) ∪ C) := by
    intro x hx
    simp only [Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact Or.inl (by simp)
    · exact Or.inr hx
  have hinter : ({a, a'} : Set α) ∩ insert a C ⊆ ({a} : Set α) := by
    intro x hx
    rcases hx with ⟨hxPair, hxMid⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxPair hxMid ⊢
    rcases hxPair with hxa | hxa'
    · exact hxa
    rcases hxMid with hxa | hxC
    · exact hxa
    have ha'C : a' ∈ C := by simpa [hxa'] using hxC
    exact (Set.disjoint_left.1 hAC (by simp) ha'C).elim
  simpa [Set.pair_comm] using
    hI.isCircuit_pair_of_mem_closure_inter_singleton
      hpairI hmiddleI hcEndpoint hcMiddle hcI hcNonloop hinter

/-- If two subsets of one independent set both span the same nonloop `e`,
then the fundamental circuit of `e` is supported on their intersection.
In particular, when the intersection is contained in a singleton `{f}`,
the pair `{e,f}` is a circuit.

This is the intrinsic form of the rank-four observation that a forced
distance-two closure incidence is an actual parallel pair rather than merely
an ambient closure relation. -/
theorem Matroid.Indep.isCircuit_pair_of_mem_closure_inter_singleton
    {I X Y : Set α} {e f : α}
    (hI : M.Indep I)
    (hXI : X ⊆ I) (hYI : Y ⊆ I)
    (heX : e ∈ M.closure X) (heY : e ∈ M.closure Y)
    (heI : e ∉ I) (heNonloop : M.IsNonloop e)
    (hXY : X ∩ Y ⊆ ({f} : Set α)) :
    M.IsCircuit ({e, f} : Set α) := by
  have heclI : e ∈ M.closure I :=
    M.closure_subset_closure hXI heX
  have hC : M.IsCircuit (M.fundCircuit e I) :=
    hI.fundCircuit_isCircuit heclI heI
  have hCX : M.fundCircuit e I ⊆ insert e X := by
    rw [M.fundCircuit_eq_sInter heclI]
    exact insert_subset_insert (sInter_subset_of_mem (by exact ⟨hXI, heX⟩))
  have hCY : M.fundCircuit e I ⊆ insert e Y := by
    rw [M.fundCircuit_eq_sInter heclI]
    exact insert_subset_insert (sInter_subset_of_mem (by exact ⟨hYI, heY⟩))
  have hCpair : M.fundCircuit e I ⊆ ({e, f} : Set α) := by
    intro x hx
    have hxX := hCX hx
    have hxY := hCY hx
    simp only [Set.mem_insert_iff] at hxX hxY
    rcases hxX with rfl | hxX
    · simp
    rcases hxY with rfl | hxY
    · simp
    have hxf : x = f := by
      exact Set.mem_singleton_iff.mp (hXY ⟨hxX, hxY⟩)
    simp [hxf]
  have heC : e ∈ M.fundCircuit e I := M.mem_fundCircuit e I
  have hfC : f ∈ M.fundCircuit e I := by
    by_contra hf
    have hCsub : M.fundCircuit e I ⊆ ({e} : Set α) := by
      intro x hx
      have hxpair := hCpair hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxpair ⊢
      rcases hxpair with hxe | hxf
      · exact hxe
      · subst x
        exact (hf hx).elim
    have hCeq : M.fundCircuit e I = ({e} : Set α) :=
      Set.Subset.antisymm hCsub (Set.singleton_subset_iff.2 heC)
    have hdep : ¬ M.Indep ({e} : Set α) := by
      rw [← hCeq]
      exact hC.not_indep
    exact hdep heNonloop.indep
  have hpairC : ({e, f} : Set α) ⊆ M.fundCircuit e I := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact heC
    · exact hfC
  have hEq : M.fundCircuit e I = ({e, f} : Set α) :=
    Set.Subset.antisymm hCpair hpairC
  rwa [hEq] at hC

end HigherRankKUM
