import Rank3KUM.TwoGap.UnequalContradiction

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/-- Remove the common singleton partner `t` from the fundamental support of `e`. -/
def ResidualSupport
    (M : Matroid α) (D : Set α) (t e : α) : Set α :=
  FundamentalSupport M D e \ {t}

@[simp] theorem mem_residualSupport
    (M : Matroid α) (D : Set α) (t e d : α) :
    d ∈ ResidualSupport M D t e ↔
      d ∈ FundamentalSupport M D e ∧ d ≠ t := by
  simp [ResidualSupport]

/-- A residual support lies in the deleted basis with the common partner removed. -/
theorem residualSupport_subset_basis_sdiff
    (M : Matroid α) {D : Set α} {t e : α}
    (hD : M.IsBase D) (heE : e ∈ M.E) (heD : e ∉ D) :
    ResidualSupport M D t e ⊆ D \ {t} := by
  intro d hd
  have hd' := (mem_residualSupport M D t e d).mp hd
  have hdD :=
    ((mem_fundamentalSupport_iff_exchange_isBase M hD heE heD).mp hd'.1).1
  exact ⟨hdD, by simpa using hd'.2⟩

/-- If the residual support is empty and `t` supports `e`, then the full support is `{t}`. -/
theorem fundamentalSupport_eq_singleton_of_residualSupport_eq_empty
    (M : Matroid α) {D : Set α} {t e : α}
    (ht : t ∈ FundamentalSupport M D e)
    (hres : ResidualSupport M D t e = ∅) :
    FundamentalSupport M D e = {t} := by
  ext d
  constructor
  · intro hd
    by_cases hdt : d = t
    · simp [hdt]
    · have hdres : d ∈ ResidualSupport M D t e :=
        (mem_residualSupport M D t e d).2 ⟨hd, hdt⟩
      rw [hres] at hdres
      exact hdres.elim
  · intro hd
    simpa only [Set.mem_singleton_iff] using hd ▸ ht

/--
A residual support is nonempty whenever `t` supports `e` and some basis
contains both `e` and `t`. If it were empty, `{e,t}` would be a circuit inside
that basis.
-/
theorem residualSupport_nonempty_of_pair_subset_basis
    (M : Matroid α) {D B : Set α} {t e : α}
    (hD : M.IsBase D) (heE : e ∈ M.E) (heD : e ∉ D)
    (ht : t ∈ FundamentalSupport M D e)
    (hB : M.IsBase B)
    (hpair : ({e, t} : Set α) ⊆ B) :
    (ResidualSupport M D t e).Nonempty := by
  by_contra hne
  have hres : ResidualSupport M D t e = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro d hd
    exact hne ⟨d, hd⟩
  have hsupp : FundamentalSupport M D e = {t} :=
    fundamentalSupport_eq_singleton_of_residualSupport_eq_empty M ht hres
  have hpairCircuit : M.IsCircuit ({e, t} : Set α) :=
    fundamentalSupport_eq_singleton_isCircuit_pair M hD heE heD hsupp
  exact (not_indep_of_isCircuit_pair_subset M hpairCircuit hpair) hB.indep

end Rank3KUM.TwoGap
