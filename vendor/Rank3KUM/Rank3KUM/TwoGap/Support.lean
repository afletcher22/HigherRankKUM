import Rank3KUM.TwoGap

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/--
The elements of `D` in the fundamental circuit of `e` over `D`.
When `D` is a basis and `e ∈ M.E \ D`, these are exactly the elements
whose replacement by `e` gives another basis.
-/
def FundamentalSupport
    (M : Matroid α) (D : Set α) (e : α) : Set α :=
  M.fundCircuit e D \ {e}

@[simp] theorem mem_fundamentalSupport
    (M : Matroid α) (D : Set α) (e d : α) :
    d ∈ FundamentalSupport M D e ↔
      d ∈ M.fundCircuit e D ∧ d ≠ e := by
  simp [FundamentalSupport]

/-- Fundamental support is the basis-exchange support. -/
theorem mem_fundamentalSupport_iff_exchange_isBase
    (M : Matroid α) {D : Set α} {e d : α}
    (hD : M.IsBase D) (heE : e ∈ M.E) (heD : e ∉ D) :
    d ∈ FundamentalSupport M D e ↔
      d ∈ D ∧ M.IsBase (exchangeSet D d e) := by
  have heclD : e ∈ M.closure D := by
    rw [hD.closure_eq]
    exact heE
  constructor
  · rintro ⟨hdC, hde⟩
    have hdD : d ∈ D := by
      have hd_insert : d ∈ insert e D :=
        (M.fundCircuit_subset_insert e D) hdC
      exact (Set.mem_insert_iff.mp hd_insert).resolve_left hde
    have hI : M.Indep (insert e D \ {d}) :=
      (hD.indep.mem_fundCircuit_iff heclD heD).mp hdC
    refine ⟨hdD, ?_⟩
    simpa [exchangeSet] using
      hD.exchange_isBase_of_indep' hdD heD hI
  · rintro ⟨hdD, hbase⟩
    have hde : d ≠ e := by
      intro h
      subst d
      exact heD hdD
    have hI : M.Indep (insert e D \ {d}) := by
      simpa [exchangeSet] using hbase.indep
    have hdC : d ∈ M.fundCircuit e D :=
      (hD.indep.mem_fundCircuit_iff heclD heD).mpr hI
    exact ⟨hdC, hde⟩

/-- Every symmetric partner lies in the corresponding fundamental support. -/
theorem symmetricPartners_subset_fundamentalSupport
    (M : Matroid α) {D B : Set α} {e : α}
    (hD : M.IsBase D) (hB : M.IsBase B)
    (heB : e ∈ B) (heD : e ∉ D) :
    SymmetricPartners M D B e ⊆ FundamentalSupport M D e := by
  intro d hd
  have heE : e ∈ M.E := hB.subset_ground heB
  have hd' := (mem_symmetricPartners M D B e d).mp hd
  exact (mem_fundamentalSupport_iff_exchange_isBase M hD heE heD).mpr
    ⟨hd'.1, hd'.2.2.1⟩

/--
If the fundamental support is the singleton `{d}`, then the fundamental
circuit itself is the two-element set `{e,d}`.
-/
theorem fundamentalSupport_eq_singleton_isCircuit_pair
    (M : Matroid α) {D : Set α} {e d : α}
    (hD : M.IsBase D) (heE : e ∈ M.E) (heD : e ∉ D)
    (hsupp : FundamentalSupport M D e = {d}) :
    M.IsCircuit ({e, d} : Set α) := by
  have hC : M.IsCircuit (M.fundCircuit e D) :=
    hD.fundCircuit_isCircuit heE heD
  have hFC : M.fundCircuit e D = ({e, d} : Set α) := by
    calc
      M.fundCircuit e D =
          insert e (M.fundCircuit e D \ {e}) := by
        rw [insert_sdiff_singleton,
          insert_eq_of_mem (M.mem_fundCircuit e D)]
      _ = insert e {d} := by
        change insert e (FundamentalSupport M D e) = insert e {d}
        rw [hsupp]
      _ = ({e, d} : Set α) := rfl
  rwa [hFC] at hC

/-- A circuit pair is dependent, so it cannot be contained in an independent set. -/
theorem not_indep_of_isCircuit_pair_subset
    (M : Matroid α) {e d : α} {I : Set α}
    (hpair : M.IsCircuit ({e, d} : Set α))
    (hsub : ({e, d} : Set α) ⊆ I) :
    ¬ M.Indep I := by
  intro hI
  exact hpair.not_indep (hI.subset hsub)

end Rank3KUM.TwoGap
