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

end LocalRepairRigidity
end HigherRankKUM
