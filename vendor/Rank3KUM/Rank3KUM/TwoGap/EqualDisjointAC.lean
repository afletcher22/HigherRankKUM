import Rank3KUM.TwoGap.EqualNonempty
import Rank3KUM.TwoGap.ResidualSupportDisjoint

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/-- The residual supports of `a` and `c` are disjoint in the equal-singleton branch. -/
theorem equal_singleton_residualSupport_a_disjoint_c
    (M : Matroid α) {D : Set α} {a b c t : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hC : M.IsBase ({a, b, c} : Set α))
    (haD : a ∉ D) (hbD : b ∉ D) (hcD : c ∉ D)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htD : t ∈ D)
    (hDtb : M.IsBase (exchangeSet D t b))
    (hXCa :
      SymmetricPartners M D ({a, b, c} : Set α) a = {t})
    (hXCc :
      SymmetricPartners M D ({a, b, c} : Set α) c = {t}) :
    Disjoint (ResidualSupport M D t a) (ResidualSupport M D t c) := by
  have hXset : ({a, c, b} : Set α) = ({a, b, c} : Set α) := by
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  have hYset : ({b, a, c} : Set α) = ({a, b, c} : Set α) := by
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  have hBridgeSet : ({c, b, a} : Set α) = ({a, b, c} : Set α) := by
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  have hX : M.IsBase ({a, c, b} : Set α) := by
    rw [hXset]
    exact hC
  have hY : M.IsBase ({b, a, c} : Set α) := by
    rw [hYset]
    exact hC
  have hBridge : M.IsBase ({c, b, a} : Set α) := by
    rw [hBridgeSet]
    exact hC
  have hXsym :
      SymmetricPartners M D ({a, c, b} : Set α) a = {t} := by
    rw [hXset]
    exact hXCa
  have hYsym :
      SymmetricPartners M D ({b, a, c} : Set α) c = {t} := by
    rw [hYset]
    exact hXCc
  exact
    residualSupport_disjoint_of_shared_bridge
      M hRank hD hX hY hBridge
      haD hcD hbD haD hcD
      hac hab hbc.symm hab.symm hbc.symm hac.symm
      htD hDtb hXsym hYsym

end Rank3KUM.TwoGap
