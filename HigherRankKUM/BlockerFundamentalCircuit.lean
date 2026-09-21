import HigherRankKUM.BlockerClosure
import HigherRankKUM.FundamentalCircuitExchange

namespace HigherRankKUM
namespace BlockerFundamentalCircuit

open Set

variable {α : Type*} {M : Matroid α} {B : Set α} {e f : α}

/-- For a basis `B`, deleting an endpoint `f` leaves a set spanning the
outside element `e` exactly when `f` is absent from the fundamental circuit
of `e` with respect to `B`.

This is the fixed-basis form of the blocker/end-point dictionary. -/
theorem Matroid.IsBase.mem_closure_sdiff_singleton_iff_not_mem_fundCircuit
    (hB : M.IsBase B) (heE : e ∈ M.E) (heB : e ∉ B) (hfB : f ∈ B) :
    e ∈ M.closure (B \ {f}) ↔ f ∉ M.fundCircuit e B := by
  have hecl : e ∈ M.closure B := by
    rw [hB.closure_eq]
    exact heE
  have hfe : f ≠ e := by
    intro hEq
    subst f
    exact heB hfB
  have hI : M.Indep (B \ {f}) :=
    hB.indep.sdiff _
  have heDiff : e ∉ B \ {f} := by
    intro he
    exact heB he.1
  have hFC :=
    hB.indep.mem_fundCircuit_iff (x := f) hecl heB
  rw [← insert_sdiff_singleton_comm hfe] at hFC
  rw [hI.insert_indep_iff_of_notMem heDiff] at hFC
  have hFC' :
      f ∈ M.fundCircuit e B ↔ e ∉ M.closure (B \ {f}) := by
    simpa [heE] using hFC
  exact not_congr hFC' |>.symm

end BlockerFundamentalCircuit
end HigherRankKUM
