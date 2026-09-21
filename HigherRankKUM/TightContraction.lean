import HigherRankKUM.Density
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Tactic

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
For a set `A` in the ground of `M / X`, contraction subtracts exactly the
rank of `X` from the rank of `A ∪ X`. The proof is basis-theoretic and does
not assume a particular ambient rank.
-/
theorem eRk_union_eq_contract_eRk_add
    (M : Matroid α) {X A : Set α}
    (hX : X ⊆ M.E)
    (hA : A ⊆ (Matroid.contract M X).E) :
    M.eRk (A ∪ X) =
      (Matroid.contract M X).eRk A + M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := (Matroid.contract M X).exists_isBasis A
  have hJ' : (Matroid.contract M I).IsBasis J A := by
    have h := hJ
    rw [hI.contract_eq_contract_delete] at h
    exact h.of_delete
  have hLift : M.IsBasis (J ∪ I) (A ∪ I) :=
    hI.indep.union_isBasis_union_of_contract_isBasis hJ'
  have hclosure :
      M.closure (A ∪ I) = M.closure (A ∪ X) :=
    M.closure_union_congr_right hI.closure_eq_closure
  have hJI : Disjoint J I := by
    rw [Set.disjoint_left]
    intro e heJ heI
    have heGround : e ∈ M.E \ I := by
      simpa using hJ'.indep.subset_ground heJ
    exact heGround.2 heI
  calc
    M.eRk (A ∪ X) = M.eRk (M.closure (A ∪ X)) :=
      (M.eRk_closure_eq _).symm
    _ = M.eRk (M.closure (A ∪ I)) :=
      congrArg M.eRk hclosure.symm
    _ = M.eRk (A ∪ I) := M.eRk_closure_eq _
    _ = (J ∪ I).encard := hLift.encard_eq_eRk.symm
    _ = J.encard + I.encard := Set.encard_union_eq hJI
    _ = (Matroid.contract M X).eRk A + M.eRk X := by
      rw [hJ.encard_eq_eRk, hI.encard_eq_eRk]

/--
A basis of a contracted set and a basis of the contraction glue to a basis of
the original matroid. This is the rank-independent matroid step behind
balanced restriction/contraction gluing.
-/
theorem isBase_union_of_isBasis_contract_isBase
    (M : Matroid α) {X I J : Set α}
    (hX : X ⊆ M.E)
    (hI : M.IsBasis I X)
    (hJ : (Matroid.contract M X).IsBase J) :
    M.IsBase (J ∪ I) := by
  have hdata := hI.contract_indep_iff.mp hJ.indep
  have hInd : M.Indep (J ∪ I) := hdata.1
  have hSpanX : M.Spanning (J ∪ X) :=
    ((Matroid.contract_spanning_iff
      (M := M) (C := X) (X := J) hX).mp hJ.spanning).1
  have hclosure :
      M.closure (J ∪ I) = M.closure (J ∪ X) :=
    M.closure_union_congr_right hI.closure_eq_closure
  have hSpanI : M.Spanning (J ∪ I) := by
    apply (Matroid.spanning_iff_closure_eq hInd.subset_ground).2
    rw [hclosure]
    exact
      (Matroid.spanning_iff_closure_eq hSpanX.subset_ground).1 hSpanX
  exact hInd.isBase_of_spanning hSpanI

/--
Uniform density with parameter `k` is inherited by contraction of any finite
tight set, with the same parameter `k`. No ambient-rank hypothesis is used.
-/
theorem UniformlyDense.contract_tight
    (M : Matroid α) (k : ℕ)
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXfinite : X.Finite) :
    UniformlyDense (Matroid.contract M X) k := by
  intro A hA
  have hAcomp : A ⊆ M.E \ X := by
    simpa using hA
  have hAXsubset : A ∪ X ⊆ M.E :=
    Set.union_subset (hAcomp.trans Set.sdiff_subset) hX.1
  have hdisjoint : Disjoint A X :=
    Set.disjoint_sdiff_left.mono_left hAcomp
  have hdense := hDense (A ∪ X) hAXsubset
  have hrank :=
    eRk_union_eq_contract_eRk_add M hX.1 hA
  have hcancel : (k : ℕ∞) * M.eRk X ≠ ⊤ := by
    rw [← hX.2]
    exact Set.encard_ne_top_iff.mpr hXfinite
  rw [Set.encard_union_eq hdisjoint, hX.2,
    hrank, mul_add] at hdense
  exact (ENat.add_le_add_iff_right hcancel).mp hdense

end

end HigherRankKUM
