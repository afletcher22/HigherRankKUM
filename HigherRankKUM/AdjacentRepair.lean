import HigherRankKUM.AdmissiblePairCycle
import Mathlib.Combinatorics.Matroid.Dual

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
      (M.contract (A.core (rightBoundaryIndex N h hN s)).IsBase Q') := by
  exact two_boundary_repair_iff_contract_bases M
    (A.core_indep hh s)
    (A.core_indep hh (rightBoundaryIndex N h hN s)) hQL hQ'R

end AdjacentRepair
end HigherRankKUM
