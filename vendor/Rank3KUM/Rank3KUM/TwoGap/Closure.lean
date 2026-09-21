import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Tactic

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/--
In a rank-three matroid, the two lines through the adjacent pairs of a basis
meet exactly in the closure of their common element.
-/
theorem closure_pair_inter_closure_pair_eq
    (M : Matroid α) {a b c : α}
    (hRank : M.eRank = 3)
    (hB : M.IsBase ({a, b, c} : Set α)) :
    M.closure ({a, b} : Set α) ∩
        M.closure ({b, c} : Set α) =
      M.closure ({b} : Set α) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxb
    have hxE : x ∈ M.E :=
      M.mem_ground_of_mem_closure hx.1
    have hbE : b ∈ M.E :=
      hB.subset_ground (by simp)
    have habE : ({a, b} : Set α) ⊆ M.E := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hB.subset_ground (by simp)
      · exact hbE
    have hcbE : ({c, b} : Set α) ⊆ M.E := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hB.subset_ground (by simp)
      · exact hbE
    have hxbE : ({x, b} : Set α) ⊆ M.E := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hxE
      · exact hbE
    have hxb_ne : x ≠ b := by
      intro h
      subst x
      exact hxb (M.mem_closure_of_mem (by simp) (by simpa using hbE))
    have hbI : M.Indep ({b} : Set α) :=
      hB.indep.subset (by intro z hz; simp_all)
    have hbxI : M.Indep ({x, b} : Set α) := by
      have hi :=
        (hbI.notMem_closure_iff_of_notMem
          (by simp [hxb_ne]) hxE).mp hxb
      simpa [insert_comm] using hi
    have hxa :
        x ∈ M.closure (insert a ({b} : Set α)) \
            M.closure ({b} : Set α) := by
      exact ⟨by simpa using hx.1, hxb⟩
    have hxc :
        x ∈ M.closure (insert c ({b} : Set α)) \
            M.closure ({b} : Set α) := by
      have hcb : ({c, b} : Set α) = ({b, c} : Set α) := by
        ext z
        simp [or_comm]
      exact ⟨by rw [hcb]; exact hx.2, hxb⟩
    have hcl_a := M.closure_insert_congr hxa
    have hcl_c := M.closure_insert_congr hxc
    have ha_cl : a ∈ M.closure ({x, b} : Set α) := by
      rw [hcl_a]
      exact M.mem_closure_of_mem (by simp) habE
    have hb_cl : b ∈ M.closure ({x, b} : Set α) :=
      M.mem_closure_of_mem (by simp) hxbE
    have hc_cl : c ∈ M.closure ({x, b} : Set α) := by
      rw [hcl_c]
      exact M.mem_closure_of_mem (by simp) hcbE
    have htriple :
        ({a, b, c} : Set α) ⊆ M.closure ({x, b} : Set α) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ha_cl
      · exact hb_cl
      · exact hc_cl
    have hground : M.E ⊆ M.closure ({x, b} : Set α) := by
      rw [← hB.closure_eq]
      exact M.closure_subset_closure_of_subset_closure htriple
    have hpairBase : M.IsBase ({x, b} : Set α) :=
      hbxI.isBase_of_ground_subset_closure hground
    have hcontra := hpairBase.encard_eq_eRank
    rw [Set.encard_pair hxb_ne, hRank] at hcontra
    norm_num at hcontra
  · intro x hx
    constructor
    · exact M.closure_subset_closure (by intro z hz; simp_all) hx
    · exact M.closure_subset_closure (by intro z hz; simp_all) hx

end Rank3KUM.TwoGap
