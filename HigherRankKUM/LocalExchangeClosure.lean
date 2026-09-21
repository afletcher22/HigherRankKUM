import Mathlib.Combinatorics.Matroid.Closure

namespace HigherRankKUM
namespace LocalExchangeClosure

open Set
open scoped Matroid

variable {α : Type*}

/-- A failed one-element exchange out of a base is exactly a closure
obstruction on the unchanged core.

If `insert a C` is a base, `d ∉ C`, and `insert d C` is dependent, then
`d` is spanned by `C`. -/
theorem mem_closure_of_failed_base_exchange
    {M : Matroid α} {C : Set α} {a d : α}
    (hB : M.IsBase (insert a C))
    (hdC : d ∉ C)
    (hdep : M.Dep (insert d C)) :
    d ∈ M.closure C := by
  have hC : M.Indep C :=
    hB.indep.subset (Set.subset_insert a C)
  exact (hC.mem_closure_iff_of_notMem hdC).2 hdep

/-- Contrapositive form: if the incoming element is not spanned by the
unchanged core, the one-element replacement remains independent. -/
theorem indep_insert_of_not_mem_closure_of_base
    {M : Matroid α} {C : Set α} {a d : α}
    (hB : M.IsBase (insert a C))
    (hdC : d ∉ C)
    (hdcl : d ∉ M.closure C) :
    M.Indep (insert d C) := by
  have hC : M.Indep C :=
    hB.indep.subset (Set.subset_insert a C)
  rw [← hC.mem_closure_iff_of_notMem hdC] at hdcl
  exact indep_of_not_dep hdcl

end LocalExchangeClosure
end HigherRankKUM
