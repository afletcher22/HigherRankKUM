import Rank3KUM.TwoGap.EqualDisjointAC

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/-- The residual supports of `a` and `b` are disjoint in the equal-singleton branch. -/
theorem equal_singleton_residualSupport_a_disjoint_b
    (M : Matroid α) {D : Set α} {a b c q t : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hC : M.IsBase ({a, b, c} : Set α))
    (hQ : M.IsBase ({b, c, q} : Set α))
    (haD : a ∉ D) (hbD : b ∉ D) (hcD : c ∉ D) (hqD : q ∉ D)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbq : b ≠ q) (hcq : c ≠ q)
    (htD : t ∈ D)
    (hDtc : M.IsBase (exchangeSet D t c))
    (hXCa :
      SymmetricPartners M D ({a, b, c} : Set α) a = {t})
    (hXQ :
      SymmetricPartners M D ({b, c, q} : Set α) b = {t}) :
    Disjoint (ResidualSupport M D t a) (ResidualSupport M D t b) := by
  have hYset : ({c, q, b} : Set α) = ({b, c, q} : Set α) := by
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  have hY : M.IsBase ({c, q, b} : Set α) := by
    rw [hYset]
    exact hQ
  have hYsym :
      SymmetricPartners M D ({c, q, b} : Set α) b = {t} := by
    rw [hYset]
    exact hXQ
  exact
    residualSupport_disjoint_of_shared_bridge
      M hRank hD hC hY hQ
      haD hbD hcD hqD hbD
      hab hac hbc hcq hbc hbq
      htD hDtc hXCa hYsym

/-- The residual supports of `b` and `c` are disjoint in the equal-singleton branch. -/
theorem equal_singleton_residualSupport_b_disjoint_c
    (M : Matroid α) {D : Set α} {p a b c t : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hP : M.IsBase ({p, a, b} : Set α))
    (hC : M.IsBase ({a, b, c} : Set α))
    (hpD : p ∉ D) (haD : a ∉ D) (hbD : b ∉ D) (hcD : c ∉ D)
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c)
    (htD : t ∈ D)
    (hDta : M.IsBase (exchangeSet D t a))
    (hXP :
      SymmetricPartners M D ({p, a, b} : Set α) b = {t})
    (hXCc :
      SymmetricPartners M D ({a, b, c} : Set α) c = {t}) :
    Disjoint (ResidualSupport M D t b) (ResidualSupport M D t c) := by
  have hXset : ({b, p, a} : Set α) = ({p, a, b} : Set α) := by
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  have hX : M.IsBase ({b, p, a} : Set α) := by
    rw [hXset]
    exact hP
  have hXsym :
      SymmetricPartners M D ({b, p, a} : Set α) b = {t} := by
    rw [hXset]
    exact hXP
  exact
    residualSupport_disjoint_of_shared_bridge
      M hRank hD hX hC hP
      hbD hpD haD hbD hcD
      hpb.symm hab.symm hpa hab hac.symm hbc.symm
      htD hDta hXsym hXCc

end Rank3KUM.TwoGap
