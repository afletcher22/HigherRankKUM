import Mathlib.Combinatorics.Matroid.Closure

namespace HigherRankKUM
namespace Rank4LocalExchangeObstruction

open Set
open scoped Matroid

variable {α : Type*}

/-- Replacing a basis element `x` by a ground element `y` outside the
basis succeeds exactly when `y` is not spanned by the remaining basis.

This is the closure form of the local one-element exchange test used by the
four-block repair program. -/
theorem exchange_isBase_iff_notMem_closure
    {M : Matroid α} {B : Set α} {x y : α}
    (hB : M.IsBase B)
    (hxB : x ∈ B)
    (hyE : y ∈ M.E)
    (hyB : y ∉ B) :
    M.IsBase (insert y (B \ {x})) ↔
      y ∉ M.closure (B \ {x}) := by
  constructor
  · intro hEx hycl
    have hI : M.Indep (B \ {x}) :=
      hB.indep.sdiff _
    have hyI : y ∉ B \ {x} := by
      intro hy
      exact hyB hy.1
    have hDep : M.Dep (insert y (B \ {x})) :=
      (hI.mem_closure_iff_of_notMem hyI).1 hycl
    exact hDep.not_indep hEx.indep
  · intro hycl
    exact hB.exchange_base_of_notMem_closure hxB hycl hyE

/-- Failure of a one-element basis exchange is exactly a closure obstruction. -/
theorem not_exchange_isBase_iff_mem_closure
    {M : Matroid α} {B : Set α} {x y : α}
    (hB : M.IsBase B)
    (hxB : x ∈ B)
    (hyE : y ∈ M.E)
    (hyB : y ∉ B) :
    (¬ M.IsBase (insert y (B \ {x}))) ↔
      y ∈ M.closure (B \ {x}) := by
  rw [exchange_isBase_iff_notMem_closure hB hxB hyE hyB]
  simp

end Rank4LocalExchangeObstruction
end HigherRankKUM
