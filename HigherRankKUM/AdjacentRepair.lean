import HigherRankKUM.AdmissiblePairCycle
import Mathlib.Combinatorics.Matroid.Dual
import Mathlib.Combinatorics.Matroid.Loop

namespace HigherRankKUM
namespace AdjacentRepair

open Set

variable {α : Type*}

/-- A proposed local re-pairing across two boundary windows is valid exactly
when the proposed left and right pieces are bases after contracting the two
unchanged boundary interiors. This is the matroid core of the adjacent-pair
repair operation; no representability or simplicity is assumed. -/
theorem two_boundary_repair_iff_contract_bases
    (M : Matroid α) {L R Q Q' : Set α}
    (hL : M.Indep L) (hR : M.Indep R)
    (hQL : Disjoint Q L) (hQ'R : Disjoint Q' R) :
    (M.IsBase (Q ∪ L) ∧ M.IsBase (Q' ∪ R)) ↔
      ((M.contract L).IsBase Q ∧ (M.contract R).IsBase Q') := by
  constructor
  · rintro ⟨hQ, hQ'⟩
    exact ⟨hL.contract_isBase_iff.2 ⟨hQ, hQL⟩,
      hR.contract_isBase_iff.2 ⟨hQ', hQ'R⟩⟩
  · rintro ⟨hQ, hQ'⟩
    exact ⟨(hL.contract_isBase_iff.1 hQ).1,
      (hR.contract_isBase_iff.1 hQ').1⟩

/-- If each boundary window is completed by a two-element pair, then both
boundary contractions have rank two. -/
theorem boundary_contract_ranks_eq_two
    (M : Matroid α) {L R : Set α} {a₀ a₁ b₀ b₁ : α}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    (hL : M.Indep L) (hR : M.Indep R)
    (hAL : Disjoint ({a₀, a₁} : Set α) L)
    (hBR : Disjoint ({b₀, b₁} : Set α) R)
    (hA : M.IsBase ({a₀, a₁} ∪ L))
    (hB : M.IsBase ({b₀, b₁} ∪ R)) :
    (M.contract L).eRank = 2 ∧ (M.contract R).eRank = 2 := by
  exact ⟨
    PairCycle.endpoint_contract_eRank_eq_two
      (a₀ := a₀) (a₁ := a₁) (b₀ := a₀) (b₁ := a₁) M ha hL hAL hA,
    PairCycle.endpoint_contract_eRank_eq_two
      (a₀ := b₀) (a₁ := b₁) (b₀ := b₀) (b₁ := b₁) M hb hR hBR hB⟩

/-- On a common four-element ground set `U`, asking that `U \ Q` be a base of
the right boundary matroid is equivalent to asking that `Q` be a base of its
dual. Thus complementary two-pair repair is a common-basis problem between
the left boundary matroid and the dual of the right one. -/
theorem complement_isBase_iff_dual_isBase
    (R : Matroid α) {U Q : Set α}
    (hE : R.E = U) (hQ : Q ⊆ U) :
    R.IsBase (U \ Q) ↔ R✶.IsBase Q := by
  have hsub : U \ Q ⊆ R.E := by
    rw [hE]
    exact Set.sdiff_subset
  rw [R.base_iff_dual_isBase_compl hsub]
  have hdiff : R.E \ (U \ Q) = Q := by
    rw [hE]
    exact Set.sdiff_sdiff_cancel_left hQ
  rw [hdiff]

/-- Explicit common-basis packaging of the previous lemma. -/
theorem complementary_bases_iff_common_base_with_dual
    (L R : Matroid α) {U Q : Set α}
    (hRE : R.E = U) (hQ : Q ⊆ U) :
    (L.IsBase Q ∧ R.IsBase (U \ Q)) ↔
      (L.IsBase Q ∧ R✶.IsBase Q) := by
  rw [complement_isBase_iff_dual_isBase R hRE hQ]

/-- In a rank-two matroid witnessed by a two-element base, any independent
pair of two distinct elements is again a base. -/
theorem pair_indep_isBase_of_pair_isBase
    (M : Matroid α) {b₀ b₁ c₀ c₁ : α}
    (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hB : M.IsBase ({b₀, b₁} : Set α))
    (hC : M.Indep ({c₀, c₁} : Set α)) :
    M.IsBase ({c₀, c₁} : Set α) := by
  apply hC.isBase_of_eRk_ge (by simp)
  rw [← hB.encard_eq_eRank, hC.eRk_eq_encard]
  simp [hb, hc]

/-- If `{b₀,b₁}` is a base and `c` is a nonloop outside that pair, then `c`
can replace at least one of the two base elements. -/
theorem exists_cross_pair_base_of_nonloop
    (M : Matroid α) {b₀ b₁ c : α}
    (hb : b₀ ≠ b₁) (hc₀ : c ≠ b₀) (hc₁ : c ≠ b₁)
    (hB : M.IsBase ({b₀, b₁} : Set α))
    (hc : M.IsNonloop c) :
    M.IsBase ({c, b₀} : Set α) ∨ M.IsBase ({c, b₁} : Set α) := by
  by_cases hcb₀ : M.IsBase ({c, b₀} : Set α)
  · exact Or.inl hcb₀
  by_cases hcb₁ : M.IsBase ({c, b₁} : Set α)
  · exact Or.inr hcb₁
  have hcB : c ∉ ({b₀, b₁} : Set α) := by
    simp [hc₀, hc₁]
  have hdep₀ : ¬ M.Indep ({c, b₀} : Set α) := by
    intro hI
    apply hcb₀
    have hI' : M.Indep (insert c (({b₀, b₁} : Set α) \ {b₁})) := by
      simpa [hb] using hI
    have hbase := hB.exchange_isBase_of_indep (e := b₁) (f := c) hcB hI'
    simpa [hb] using hbase
  have hdep₁ : ¬ M.Indep ({c, b₁} : Set α) := by
    intro hI
    apply hcb₁
    have hI' : M.Indep (insert c (({b₀, b₁} : Set α) \ {b₀})) := by
      simpa [hb] using hI
    have hbase := hB.exchange_isBase_of_indep (e := b₀) (f := c) hcB hI'
    simpa [hb] using hbase
  have hb₀n : M.IsNonloop b₀ := hB.indep.isNonloop_of_mem (by simp)
  have hb₁n : M.IsNonloop b₁ := hB.indep.isNonloop_of_mem (by simp)
  have hcl₀ : M.closure {c} = M.closure {b₀} :=
    (hc.closure_eq_closure_iff_eq_or_dep hb₀n).2 (Or.inr hdep₀)
  have hcl₁ : M.closure {c} = M.closure {b₁} :=
    (hc.closure_eq_closure_iff_eq_or_dep hb₁n).2 (Or.inr hdep₁)
  have hcl : M.closure {b₀} = M.closure {b₁} := hcl₀.symm.trans hcl₁
  rcases (hb₀n.closure_eq_closure_iff_eq_or_dep hb₁n).1 hcl with hEq | hDep
  · exact (hb hEq).elim
  · exact (hDep hB.indep).elim

/-- Parallel nonloops are interchangeable inside a two-element base. -/
theorem pair_isBase_of_parallel_nonloops
    (M : Matroid α) {c₀ c₁ b : α}
    (hc : c₀ ≠ c₁) (hc₀b : c₀ ≠ b) (hc₁b : c₁ ≠ b)
    (hc₀ : M.IsNonloop c₀) (hc₁ : M.IsNonloop c₁)
    (hcl : M.closure {c₀} = M.closure {c₁})
    (hB : M.IsBase ({c₀, b} : Set α)) :
    M.IsBase ({c₁, b} : Set α) := by
  have hb : M.IsNonloop b := hB.indep.isNonloop_of_mem (by simp)
  have hI : M.Indep ({c₁, b} : Set α) := by
    by_contra hDep
    have hcl₁b : M.closure {c₁} = M.closure {b} :=
      (hc₁.closure_eq_closure_iff_eq_or_dep hb).2 (Or.inr hDep)
    have hcl₀b : M.closure {c₀} = M.closure {b} := hcl.trans hcl₁b
    rcases (hc₀.closure_eq_closure_iff_eq_or_dep hb).1 hcl₀b with hEq | hDep₀
    · exact hc₀b hEq
    · exact hDep₀ hB.indep
  exact pair_indep_isBase_of_pair_isBase M hc₀b hc₁b hB hI

/-- Let `B={b₀,b₁}` and `C={c₀,c₁}` be disjoint bases of `L`, and let `B`
also be a base of `R`. If `B` is the unique common base of `L` and `R`,
then at least one element of `C` is a loop of `R`.

This is the rank-two local-rigidity statement used by the adjacent-repair
analysis. It is purely matroidal and assumes neither simplicity nor
representability. -/
theorem unique_common_pair_base_forces_loop
    (L R : Matroid α) {b₀ b₁ c₀ c₁ : α}
    (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hdisj : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hLB : L.IsBase ({b₀, b₁} : Set α))
    (hLC : L.IsBase ({c₀, c₁} : Set α))
    (hRB : R.IsBase ({b₀, b₁} : Set α))
    (hc₀R : c₀ ∈ R.E) (hc₁R : c₁ ∈ R.E)
    (hunique : ∀ Q : Set α, L.IsBase Q → R.IsBase Q → Q = {b₀, b₁}) :
    R.IsLoop c₀ ∨ R.IsLoop c₁ := by
  by_cases hc₀loop : R.IsLoop c₀
  · exact Or.inl hc₀loop
  by_cases hc₁loop : R.IsLoop c₁
  · exact Or.inr hc₁loop
  exfalso
  have hc₀n : R.IsNonloop c₀ := ⟨hc₀R, hc₀loop⟩
  have hc₁n : R.IsNonloop c₁ := ⟨hc₁R, hc₁loop⟩
  have hc₀C : c₀ ∈ ({c₀, c₁} : Set α) := by simp
  have hc₁C : c₁ ∈ ({c₀, c₁} : Set α) := by simp
  have hc₀notB : c₀ ∉ ({b₀, b₁} : Set α) := by
    intro hmem
    exact Set.disjoint_left.1 hdisj hmem hc₀C
  have hc₁notB : c₁ ∉ ({b₀, b₁} : Set α) := by
    intro hmem
    exact Set.disjoint_left.1 hdisj hmem hc₁C
  have hb₀notC : b₀ ∉ ({c₀, c₁} : Set α) := by
    intro hmem
    exact Set.disjoint_left.1 hdisj (by simp) hmem
  have hb₁notC : b₁ ∉ ({c₀, c₁} : Set α) := by
    intro hmem
    exact Set.disjoint_left.1 hdisj (by simp) hmem
  have hc₀b₀ : c₀ ≠ b₀ := by
    intro hEq
    apply hc₀notB
    simp [hEq]
  have hc₀b₁ : c₀ ≠ b₁ := by
    intro hEq
    apply hc₀notB
    simp [hEq]
  have hc₁b₀ : c₁ ≠ b₀ := by
    intro hEq
    apply hc₁notB
    simp [hEq]
  have hc₁b₁ : c₁ ≠ b₁ := by
    intro hEq
    apply hc₁notB
    simp [hEq]
  have hCnotBase : ¬ R.IsBase ({c₀, c₁} : Set α) := by
    intro hRC
    have hEq := hunique ({c₀, c₁} : Set α) hLC hRC
    exact hc₀notB (hEq ▸ hc₀C)
  have hCdep : ¬ R.Indep ({c₀, c₁} : Set α) := by
    intro hI
    exact hCnotBase (pair_indep_isBase_of_pair_isBase R hb hc hRB hI)
  have hcl : R.closure {c₀} = R.closure {c₁} :=
    (hc₀n.closure_eq_closure_iff_eq_or_dep hc₁n).2 (Or.inr hCdep)
  have hcross := exists_cross_pair_base_of_nonloop R hb hc₀b₀ hc₀b₁ hRB hc₀n
  rcases hcross with hRc₀b₀ | hRc₀b₁
  · have hRc₁b₀ : R.IsBase ({c₁, b₀} : Set α) :=
      pair_isBase_of_parallel_nonloops R hc hc₀b₀ hc₁b₀ hc₀n hc₁n hcl hRc₀b₀
    obtain ⟨y, hy, hLy⟩ := hLB.exchange hLC ⟨by simp, hb₁notC⟩
    have hyC : y = c₀ ∨ y = c₁ := by
      simpa using hy.1
    rcases hyC with rfl | rfl
    · have hL : L.IsBase ({c₀, b₀} : Set α) := by
        simpa [hb] using hLy
      have hEq := hunique ({c₀, b₀} : Set α) hL hRc₀b₀
      exact hc₀notB (by rw [← hEq]; simp)
    · have hL : L.IsBase ({c₁, b₀} : Set α) := by
        simpa [hb] using hLy
      have hEq := hunique ({c₁, b₀} : Set α) hL hRc₁b₀
      exact hc₁notB (by rw [← hEq]; simp)
  · have hRc₁b₁ : R.IsBase ({c₁, b₁} : Set α) :=
      pair_isBase_of_parallel_nonloops R hc hc₀b₁ hc₁b₁ hc₀n hc₁n hcl hRc₀b₁
    obtain ⟨y, hy, hLy⟩ := hLB.exchange hLC ⟨by simp, hb₀notC⟩
    have hyC : y = c₀ ∨ y = c₁ := by
      simpa using hy.1
    rcases hyC with rfl | rfl
    · have hL : L.IsBase ({c₀, b₁} : Set α) := by
        simpa [hb] using hLy
      have hEq := hunique ({c₀, b₁} : Set α) hL hRc₀b₁
      exact hc₀notB (by rw [← hEq]; simp)
    · have hL : L.IsBase ({c₁, b₁} : Set α) := by
        simpa [hb] using hLy
      have hEq := hunique ({c₁, b₁} : Set α) hL hRc₁b₁
      exact hc₁notB (by rw [← hEq]; simp)

/-- Dual form suited to adjacent repair: if `B` is the unique common base of
`L` and `R✶`, then one element of the complementary `L`-base is a coloop of
`R`.  In an application `R` should be the right boundary matroid restricted
to the four locally moved elements. -/
theorem unique_common_pair_base_forces_right_coloop
    (L R : Matroid α) {b₀ b₁ c₀ c₁ : α}
    (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hdisj : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hLB : L.IsBase ({b₀, b₁} : Set α))
    (hLC : L.IsBase ({c₀, c₁} : Set α))
    (hRB : R✶.IsBase ({b₀, b₁} : Set α))
    (hc₀R : c₀ ∈ R✶.E) (hc₁R : c₁ ∈ R✶.E)
    (hunique : ∀ Q : Set α, L.IsBase Q → R✶.IsBase Q → Q = {b₀, b₁}) :
    R.IsColoop c₀ ∨ R.IsColoop c₁ := by
  exact unique_common_pair_base_forces_loop L R✶ hb hc hdisj hLB hLC hRB hc₀R hc₁R hunique

/-- The pair that finishes the left boundary window of an adjacent re-pairing
whose left unchanged core begins immediately after `s`. -/
def leftBoundaryIndex (N h : ℕ) (hN : 0 < N) (s : Fin N) : Fin N :=
  cyclicIndex N hN s h

/-- The adjacent pair on the right side of the same local re-pairing. -/
def rightBoundaryIndex (N h : ℕ) (hN : 0 < N) (s : Fin N) : Fin N :=
  cyclicIndex N hN s (h + 1)

/-- In an admissible pair cycle, the two contractions governing an adjacent
re-pairing are both rank two. The left interior is `A.core s`; the right
interior is the core beginning at the right modified pair. -/
theorem admissible_boundary_contract_ranks_eq_two
    {M : Matroid α} {N h : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N h hN)
    (hh : 0 < h) (hhN : h < N) (s : Fin N) :
    (M.contract (A.core s)).eRank = 2 ∧
      (M.contract (A.core (rightBoundaryIndex N h hN s))).eRank = 2 := by
  let i := leftBoundaryIndex N h hN s
  let j := rightBoundaryIndex N h hN s
  have hiDis : Disjoint
      ({A.element i false, A.element i true} : Set α) (A.core s) := by
    simpa [i, leftBoundaryIndex, AdmissiblePairCycle.Data.block,
      AdmissiblePairCycle.pairSet] using
      A.endpoint_block_disjoint_core hh hhN s
  have hiBase : M.IsBase
      ({A.element i false, A.element i true} ∪ A.core s) := by
    simpa [i, leftBoundaryIndex, AdmissiblePairCycle.Data.block,
      AdmissiblePairCycle.pairSet] using A.endpoint_basis_right hh s
  have hjDis : Disjoint
      ({A.element j false, A.element j true} : Set α) (A.core j) := by
    simpa [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      A.block_disjoint_core hh hhN j
  have hjBase : M.IsBase
      ({A.element j false, A.element j true} ∪ A.core j) := by
    simpa [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet] using
      A.endpoint_basis_left hh j
  have hranks := boundary_contract_ranks_eq_two M
    (A.element_ne i) (A.element_ne j)
    (A.core_indep hh s) (A.core_indep hh j)
    hiDis hjDis hiBase hjBase
  simpa [j, rightBoundaryIndex] using hranks

/-- Cycle-specific form of the two-boundary repair criterion. This theorem
isolates the only two basis tests a proposed local re-pairing must satisfy;
it does not assert that such a re-pairing exists. -/
theorem admissible_two_boundary_repair_iff_contract_bases
    {M : Matroid α} {N h : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N h hN)
    (hh : 0 < h) (s : Fin N) {Q Q' : Set α}
    (hQL : Disjoint Q (A.core s))
    (hQ'R : Disjoint Q' (A.core (rightBoundaryIndex N h hN s))) :
    ((M.IsBase (Q ∪ A.core s)) ∧
      (M.IsBase (Q' ∪ A.core (rightBoundaryIndex N h hN s)))) ↔
    ((M.contract (A.core s)).IsBase Q ∧
      (M.contract (A.core (rightBoundaryIndex N h hN s))).IsBase Q') := by
  exact two_boundary_repair_iff_contract_bases M
    (A.core_indep hh s)
    (A.core_indep hh (rightBoundaryIndex N h hN s)) hQL hQ'R

end AdjacentRepair
end HigherRankKUM
