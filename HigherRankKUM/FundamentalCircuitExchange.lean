import Mathlib.Combinatorics.Matroid.Circuit

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

end HigherRankKUM
