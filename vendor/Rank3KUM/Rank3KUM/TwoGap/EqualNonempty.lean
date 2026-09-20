import Rank3KUM.TwoGap.EqualSupport

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/-- In the equal-singleton branch, all three residual fundamental supports are nonempty. -/
theorem equal_singleton_residualSupports_nonempty
    (M : Matroid α) {D : Set α} {p a b c t : α}
    (hD : M.IsBase D)
    (hP : M.IsBase ({p, a, b} : Set α))
    (hC : M.IsBase ({a, b, c} : Set α))
    (haD : a ∉ D) (hbD : b ∉ D) (hcD : c ∉ D)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hXP :
      SymmetricPartners M D ({p, a, b} : Set α) b = {t})
    (hXCa :
      SymmetricPartners M D ({a, b, c} : Set α) a = {t})
    (hXCc :
      SymmetricPartners M D ({a, b, c} : Set α) c = {t}) :
    (ResidualSupport M D t a).Nonempty ∧
      (ResidualSupport M D t b).Nonempty ∧
      (ResidualSupport M D t c).Nonempty := by
  have htXP :
      t ∈ SymmetricPartners M D ({p, a, b} : Set α) b := by
    rw [hXP]
    simp
  have htXCa :
      t ∈ SymmetricPartners M D ({a, b, c} : Set α) a := by
    rw [hXCa]
    simp
  have htXCc :
      t ∈ SymmetricPartners M D ({a, b, c} : Set α) c := by
    rw [hXCc]
    simp

  have htXP' :=
    (mem_symmetricPartners M D ({p, a, b} : Set α) b t).mp htXP
  have htD : t ∈ D := htXP'.1
  have hta : t ≠ a := by
    intro h
    apply haD
    rw [← h]
    exact htD
  have htb : t ≠ b := by
    intro h
    apply hbD
    rw [← h]
    exact htD
  have htc : t ≠ c := by
    intro h
    apply hcD
    rw [← h]
    exact htD

  have htSuppA : t ∈ FundamentalSupport M D a :=
    symmetricPartners_subset_fundamentalSupport M hD hC
      (by simp) haD htXCa
  have htSuppB : t ∈ FundamentalSupport M D b :=
    symmetricPartners_subset_fundamentalSupport M hD hP
      (by simp) hbD htXP
  have htSuppC : t ∈ FundamentalSupport M D c :=
    symmetricPartners_subset_fundamentalSupport M hD hC
      (by simp) hcD htXCc

  have htXCa' :=
    (mem_symmetricPartners M D ({a, b, c} : Set α) a t).mp htXCa
  have htXCc' :=
    (mem_symmetricPartners M D ({a, b, c} : Set α) c t).mp htXCc
  have hBaseTBC : M.IsBase ({t, b, c} : Set α) := by
    rw [← exchangeSet_triple_remove_first hab hac hta]
    exact htXCa'.2.2.2
  have hBaseABT : M.IsBase ({a, b, t} : Set α) := by
    rw [← exchangeSet_triple_remove_third hac.symm hbc.symm htc]
    exact htXCc'.2.2.2

  have hPairAT : ({a, t} : Set α) ⊆ ({a, b, t} : Set α) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  have hPairBT : ({b, t} : Set α) ⊆ ({a, b, t} : Set α) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hPairCT : ({c, t} : Set α) ⊆ ({t, b, c} : Set α) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

  refine ⟨?_, ?_, ?_⟩
  · exact residualSupport_nonempty_of_pair_subset_basis
      M hD (hC.subset_ground (by simp)) haD htSuppA hBaseABT hPairAT
  · exact residualSupport_nonempty_of_pair_subset_basis
      M hD (hP.subset_ground (by simp)) hbD htSuppB hBaseABT hPairBT
  · exact residualSupport_nonempty_of_pair_subset_basis
      M hD (hC.subset_ground (by simp)) hcD htSuppC hBaseTBC hPairCT

end Rank3KUM.TwoGap
