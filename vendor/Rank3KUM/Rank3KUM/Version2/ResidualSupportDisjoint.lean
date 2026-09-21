import Rank3KUM.TwoGap.ResidualSupportDisjoint

namespace Rank3KUM.Version2

open Set
open Rank3KUM.TwoGap

variable {α : Type*}

/--
Paper v2, Lemma 7.20: the common residual-support disjointness argument.

The active two-gap proof now uses the shared theorem directly; this declaration
is retained as the paper-facing version-2 correspondence.
-/
theorem residualSupport_disjoint_of_shared_bridge
    (M : Matroid α)
    {D : Set α} {x u s v y t : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hX : M.IsBase ({x, u, s} : Set α))
    (hY : M.IsBase ({s, v, y} : Set α))
    (hBridge : M.IsBase ({u, s, v} : Set α))
    (hxD : x ∉ D) (huD : u ∉ D) (hsD : s ∉ D)
    (hvD : v ∉ D) (hyD : y ∉ D)
    (hxu : x ≠ u) (hxs : x ≠ s) (hus : u ≠ s)
    (hsv : s ≠ v) (hys : y ≠ s) (hyv : y ≠ v)
    (htD : t ∈ D)
    (hDts : M.IsBase (exchangeSet D t s))
    (hXsym :
      SymmetricPartners M D ({x, u, s} : Set α) x = {t})
    (hYsym :
      SymmetricPartners M D ({s, v, y} : Set α) y = {t}) :
    Disjoint (ResidualSupport M D t x) (ResidualSupport M D t y) := by
  exact
    Rank3KUM.TwoGap.residualSupport_disjoint_of_shared_bridge
      M hRank hD hX hY hBridge
      hxD huD hsD hvD hyD
      hxu hxs hus hsv hys hyv
      htD hDts hXsym hYsym

#print axioms Rank3KUM.Version2.residualSupport_disjoint_of_shared_bridge

end Rank3KUM.Version2
