import HigherRankKUM.AdjacentRepair

namespace HigherRankKUM
namespace LocalRepairRigidity

open Set

variable {α : Type*}

/-- On an exact four-element local ground, if `drop` is not a coloop then a
base `{keep, drop}` can exchange `drop` for one of the two elements on the
opposite side. This is the column-support companion to
`AdjacentRepair.exists_cross_pair_base_of_nonloop`. -/
theorem exists_cross_pair_base_of_not_coloop
    (M : Matroid α) {keep drop c₀ c₁ : α}
    (hkd : keep ≠ drop)
    (hE : M.E = ({keep, drop} : Set α) ∪ ({c₀, c₁} : Set α))
    (hB : M.IsBase ({keep, drop} : Set α))
    (hdrop : ¬ M.IsColoop drop) :
    M.IsBase ({c₀, keep} : Set α) ∨ M.IsBase ({c₁, keep} : Set α) := by
  have hdrop' := hdrop
  simp only [Matroid.isColoop_iff_forall_mem_isBase, not_forall, exists_prop] at hdrop'
  obtain ⟨D, hD, hdropD⟩ := hdrop'
  obtain ⟨y, hy, hY⟩ := hB.exchange hD ⟨by simp, hdropD⟩
  have hyE : y ∈ M.E := hD.subset_ground hy.1
  have hyC : y ∈ ({c₀, c₁} : Set α) := by
    rw [hE] at hyE
    rcases hyE with hyB | hyC
    · exact (hy.2 hyB).elim
    · exact hyC
  have hyCases : y = c₀ ∨ y = c₁ := by
    simpa using hyC
  have hY' : M.IsBase ({y, keep} : Set α) := by
    simpa [hkd] using hY
  rcases hyCases with hy₀ | hy₁
  · exact Or.inl (by simpa [hy₀] using hY')
  · exact Or.inr (by simpa [hy₁] using hY')

/-- Four-element local rigidity. Let `B = {b₀,b₁}` be a common base of two
rank-two matroids `L` and `S` on the same four-element local ground
`B ∪ {c₀,c₁}`. If `B` is their unique common base, then either an opposite-side
element is a loop of `L`, or a current-base element is a coloop of `S`.

In adjacent repair one takes `S` to be the dual of the right boundary
matroid. Thus the coloop alternative becomes a loop on the right boundary.
No simplicity or representability hypothesis is used. -/
theorem unique_common_pair_base_forces_loop_or_coloop
    (L S : Matroid α) {b₀ b₁ c₀ c₁ : α}
    (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hdisj : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hLE : L.E = ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α))
    (hSE : S.E = ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α))
    (hLB : L.IsBase ({b₀, b₁} : Set α))
    (hSB : S.IsBase ({b₀, b₁} : Set α))
    (hunique : ∀ Q : Set α, L.IsBase Q → S.IsBase Q → Q = {b₀, b₁}) :
    L.IsLoop c₀ ∨ L.IsLoop c₁ ∨ S.IsColoop b₀ ∨ S.IsColoop b₁ := by
  by_cases hc₀loop : L.IsLoop c₀
  · exact Or.inl hc₀loop
  by_cases hc₁loop : L.IsLoop c₁
  · exact Or.inr (Or.inl hc₁loop)
  by_cases hb₀coloop : S.IsColoop b₀
  · exact Or.inr (Or.inr (Or.inl hb₀coloop))
  by_cases hb₁coloop : S.IsColoop b₁
  · exact Or.inr (Or.inr (Or.inr hb₁coloop))
  exfalso
  have hc₀L : c₀ ∈ L.E := by rw [hLE]; simp
  have hc₁L : c₁ ∈ L.E := by rw [hLE]; simp
  have hc₀n : L.IsNonloop c₀ := ⟨hc₀loop, hc₀L⟩
  have hc₁n : L.IsNonloop c₁ := ⟨hc₁loop, hc₁L⟩
  have hc₀notB : c₀ ∉ ({b₀, b₁} : Set α) := by
    intro hmem
    exact Set.disjoint_left.1 hdisj hmem (by simp)
  have hc₁notB : c₁ ∉ ({b₀, b₁} : Set α) := by
    intro hmem
    exact Set.disjoint_left.1 hdisj hmem (by simp)
  have hc₀b₀ : c₀ ≠ b₀ := by
    intro hEq; apply hc₀notB; simp [hEq]
  have hc₀b₁ : c₀ ≠ b₁ := by
    intro hEq; apply hc₀notB; simp [hEq]
  have hc₁b₀ : c₁ ≠ b₀ := by
    intro hEq; apply hc₁notB; simp [hEq]
  have hc₁b₁ : c₁ ≠ b₁ := by
    intro hEq; apply hc₁notB; simp [hEq]
  have hL0 := AdjacentRepair.exists_cross_pair_base_of_nonloop
    L hb hc₀b₀ hc₀b₁ hLB hc₀n
  have hL1 := AdjacentRepair.exists_cross_pair_base_of_nonloop
    L hb hc₁b₀ hc₁b₁ hLB hc₁n
  have hS0 := exists_cross_pair_base_of_not_coloop
    S hb hSE hSB hb₁coloop
  have hSE' : S.E = ({b₁, b₀} : Set α) ∪ ({c₀, c₁} : Set α) := by
    simpa [pair_comm] using hSE
  have hSB' : S.IsBase ({b₁, b₀} : Set α) := by
    simpa [pair_comm] using hSB
  have hS1 := exists_cross_pair_base_of_not_coloop
    S hb.symm hSE' hSB' hb₀coloop
  have h00 (hL : L.IsBase ({c₀, b₀} : Set α))
      (hS : S.IsBase ({c₀, b₀} : Set α)) : False := by
    have hEq := hunique ({c₀, b₀} : Set α) hL hS
    apply hc₀notB
    rw [← hEq]
    simp
  have h01 (hL : L.IsBase ({c₀, b₁} : Set α))
      (hS : S.IsBase ({c₀, b₁} : Set α)) : False := by
    have hEq := hunique ({c₀, b₁} : Set α) hL hS
    apply hc₀notB
    rw [← hEq]
    simp
  have h10 (hL : L.IsBase ({c₁, b₀} : Set α))
      (hS : S.IsBase ({c₁, b₀} : Set α)) : False := by
    have hEq := hunique ({c₁, b₀} : Set α) hL hS
    apply hc₁notB
    rw [← hEq]
    simp
  have h11 (hL : L.IsBase ({c₁, b₁} : Set α))
      (hS : S.IsBase ({c₁, b₁} : Set α)) : False := by
    have hEq := hunique ({c₁, b₁} : Set α) hL hS
    apply hc₁notB
    rw [← hEq]
    simp
  rcases hL0 with hL00 | hL01
  · rcases hL1 with hL10 | hL11
    · rcases hS0 with hS00 | hS10
      · exact h00 hL00 hS00
      · exact h10 hL10 hS10
    · rcases hS0 with hS00 | hS10
      · exact h00 hL00 hS00
      · rcases hS1 with hS01 | hS11
        · have hLCind : L.Indep ({c₀, c₁} : Set α) := by
            by_contra hdep
            have hcl : L.closure {c₀} = L.closure {c₁} :=
              (hc₀n.closure_eq_closure_iff_eq_or_dep hc₁n).2 (Or.inr hdep)
            have hL10' := AdjacentRepair.pair_isBase_of_parallel_nonloops
              L hc hc₀b₀ hc₁b₀ hc₀n hc₁n hcl hL00
            exact h10 hL10' hS10
          have hLC : L.IsBase ({c₀, c₁} : Set α) :=
            AdjacentRepair.pair_indep_isBase_of_pair_isBase L hb hc hLB hLCind
          have hSc₀n : S.IsNonloop c₀ := hS01.indep.isNonloop_of_mem (by simp)
          have hSc₁n : S.IsNonloop c₁ := hS10.indep.isNonloop_of_mem (by simp)
          have hSCind : S.Indep ({c₀, c₁} : Set α) := by
            by_contra hdep
            have hcl : S.closure {c₀} = S.closure {c₁} :=
              (hSc₀n.closure_eq_closure_iff_eq_or_dep hSc₁n).2 (Or.inr hdep)
            have hS11' := AdjacentRepair.pair_isBase_of_parallel_nonloops
              S hc hc₀b₁ hc₁b₁ hSc₀n hSc₁n hcl hS01
            exact h11 hL11 hS11'
          have hSC : S.IsBase ({c₀, c₁} : Set α) :=
            AdjacentRepair.pair_indep_isBase_of_pair_isBase S hb hc hSB hSCind
          have hEq := hunique ({c₀, c₁} : Set α) hLC hSC
          exact hc₀notB (by rw [← hEq]; simp)
        · exact h11 hL11 hS11
  · rcases hL1 with hL10 | hL11
    · rcases hS0 with hS00 | hS10
      · rcases hS1 with hS01 | hS11
        · exact h01 hL01 hS01
        · have hLCind : L.Indep ({c₀, c₁} : Set α) := by
            by_contra hdep
            have hcl : L.closure {c₀} = L.closure {c₁} :=
              (hc₀n.closure_eq_closure_iff_eq_or_dep hc₁n).2 (Or.inr hdep)
            have hL11' := AdjacentRepair.pair_isBase_of_parallel_nonloops
              L hc hc₀b₁ hc₁b₁ hc₀n hc₁n hcl hL01
            exact h11 hL11' hS11
          have hLC : L.IsBase ({c₀, c₁} : Set α) :=
            AdjacentRepair.pair_indep_isBase_of_pair_isBase L hb hc hLB hLCind
          have hSc₀n : S.IsNonloop c₀ := hS00.indep.isNonloop_of_mem (by simp)
          have hSc₁n : S.IsNonloop c₁ := hS11.indep.isNonloop_of_mem (by simp)
          have hSCind : S.Indep ({c₀, c₁} : Set α) := by
            by_contra hdep
            have hcl : S.closure {c₀} = S.closure {c₁} :=
              (hSc₀n.closure_eq_closure_iff_eq_or_dep hSc₁n).2 (Or.inr hdep)
            have hS10' := AdjacentRepair.pair_isBase_of_parallel_nonloops
              S hc hc₀b₀ hc₁b₀ hSc₀n hSc₁n hcl hS00
            exact h10 hL10 hS10'
          have hSC : S.IsBase ({c₀, c₁} : Set α) :=
            AdjacentRepair.pair_indep_isBase_of_pair_isBase S hb hc hSB hSCind
          have hEq := hunique ({c₀, c₁} : Set α) hLC hSC
          exact hc₀notB (by rw [← hEq]; simp)
      · exact h10 hL10 hS10
    · rcases hS1 with hS01 | hS11
      · exact h01 hL01 hS01
      · exact h11 hL11 hS11

end LocalRepairRigidity
end HigherRankKUM
