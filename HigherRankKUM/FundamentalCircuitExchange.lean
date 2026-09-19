import Mathlib.Combinatorics.Matroid.Loop

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
