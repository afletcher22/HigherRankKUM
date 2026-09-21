import HigherRankKUM.LocalRepairRigidity

namespace HigherRankKUM
namespace LocalRepairBoundary

open Set

variable {α : Type*}

/-- Boundary form of four-element local rigidity.  If `B = {b₀,b₁}` is the
unique common base of the left boundary matroid `L` and the dual of the right
boundary matroid `R`, then at least one opposite-side element is a loop of
`L`, or at least one current-base element is a loop of `R`.

This is the form used by adjacent re-pairing: the right-side coloop produced
by `unique_common_pair_base_forces_loop_or_coloop` becomes a loop after
undoing the dual. -/
theorem unique_common_pair_with_dual_forces_boundary_loop
    (L R : Matroid α) {b₀ b₁ c₀ c₁ : α}
    (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hdisj : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hLE : L.E = ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α))
    (hRE : R.E = ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α))
    (hLB : L.IsBase ({b₀, b₁} : Set α))
    (hRdualB : R✶.IsBase ({b₀, b₁} : Set α))
    (hunique : ∀ Q : Set α, L.IsBase Q → R✶.IsBase Q → Q = {b₀, b₁}) :
    L.IsLoop c₀ ∨ L.IsLoop c₁ ∨ R.IsLoop b₀ ∨ R.IsLoop b₁ := by
  have hREdual : R✶.E = ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α) := by
    simpa using hRE
  have h := LocalRepairRigidity.unique_common_pair_base_forces_loop_or_coloop
    L R✶ hb hc hdisj hLE hREdual hLB hRdualB hunique
  simpa [Matroid.IsColoop] using h

end LocalRepairBoundary
end HigherRankKUM
