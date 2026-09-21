import HigherRankKUM.LocalRepairRigidity
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace HigherRankKUM
namespace LocalRepairFivePairRigidity

open Set

variable {α : Type*}

/-- A two-element subset of a four-element ground is either the distinguished
pair or one of the five explicit alternatives. -/
theorem two_subset_four_pair_classification
    {b₀ b₁ c₀ c₁ : α}
    (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hdisj : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    {Q : Set α}
    (hQcard : Q.encard = 2)
    (hQsub : Q ⊆ ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α)) :
    Q = {b₀, b₁} ∨
    Q = {b₀, c₀} ∨
    Q = {b₀, c₁} ∨
    Q = {b₁, c₀} ∨
    Q = {b₁, c₁} ∨
    Q = {c₀, c₁} := by
  obtain ⟨x, y, hxy, rfl⟩ := Set.encard_eq_two.mp hQcard
  have hxU :
      x ∈ ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α) :=
    hQsub (by simp)
  have hyU :
      y ∈ ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α) :=
    hQsub (by simp)
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hxU hyU
  rcases hxU with (hx0 | hx1) | (hxc0 | hxc1)
  · subst x
    rcases hyU with (hy0 | hy1) | (hyc0 | hyc1)
    · exact (hxy hy0.symm).elim
    · subst y
      exact Or.inl rfl
    · subst y
      exact Or.inr (Or.inl rfl)
    · subst y
      exact Or.inr (Or.inr (Or.inl rfl))
  · subst x
    rcases hyU with (hy0 | hy1) | (hyc0 | hyc1)
    · subst y
      exact Or.inl (Set.pair_comm b₁ b₀)
    · exact (hxy hy1.symm).elim
    · subst y
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · subst y
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · subst x
    rcases hyU with (hy0 | hy1) | (hyc0 | hyc1)
    · subst y
      exact Or.inr (Or.inl (Set.pair_comm c₀ b₀))
    · subst y
      exact Or.inr (Or.inr (Or.inr (Or.inl (Set.pair_comm c₀ b₁))))
    · exact (hxy hyc0.symm).elim
    · subst y
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · subst x
    rcases hyU with (hy0 | hy1) | (hyc0 | hyc1)
    · subst y
      exact Or.inr (Or.inr (Or.inl (Set.pair_comm c₁ b₀)))
    · subst y
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Set.pair_comm c₁ b₁)))))
    · subst y
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Set.pair_comm c₁ c₀)))))
    · exact (hxy hyc1.symm).elim

/-- Four-element local rigidity in the form directly exposed by local moves.

The distinguished pair B={b₀,b₁} is a common base of two rank-two matroids
on B union {c₀,c₁}. If none of the five other two-element subsets is a common
base, then the usual loop/coloop rigidity conclusion follows.

This is equivalent to uniqueness of B, but is much easier to connect to a
finite move family: each alternative pair can be tested explicitly. -/
theorem no_five_alternative_common_pairs_forces_loop_or_coloop
    (L S : Matroid α) {b₀ b₁ c₀ c₁ : α}
    (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hdisj : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hLE : L.E = ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α))
    (hSE : S.E = ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α))
    (hLB : L.IsBase ({b₀, b₁} : Set α))
    (hSB : S.IsBase ({b₀, b₁} : Set α))
    (h00 : ¬ (L.IsBase ({b₀, c₀} : Set α) ∧
      S.IsBase ({b₀, c₀} : Set α)))
    (h01 : ¬ (L.IsBase ({b₀, c₁} : Set α) ∧
      S.IsBase ({b₀, c₁} : Set α)))
    (h10 : ¬ (L.IsBase ({b₁, c₀} : Set α) ∧
      S.IsBase ({b₁, c₀} : Set α)))
    (h11 : ¬ (L.IsBase ({b₁, c₁} : Set α) ∧
      S.IsBase ({b₁, c₁} : Set α)))
    (hcc : ¬ (L.IsBase ({c₀, c₁} : Set α) ∧
      S.IsBase ({c₀, c₁} : Set α))) :
    L.IsLoop c₀ ∨ L.IsLoop c₁ ∨ S.IsColoop b₀ ∨ S.IsColoop b₁ := by
  apply LocalRepairRigidity.unique_common_pair_base_forces_loop_or_coloop
    L S hb hc hdisj hLE hSE hLB hSB
  intro Q hLQ hSQ
  have hQcard : Q.encard = 2 := by
    rw [hLQ.encard_eq_eRank, ← hLB.encard_eq_eRank, Set.encard_pair hb]
  have hQsub :
      Q ⊆ ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α) := by
    rw [← hLE]
    exact hLQ.subset_ground
  rcases two_subset_four_pair_classification hb hc hdisj hQcard hQsub with
      hB | hB0 | hB1 | hC0 | hC1 | hC
  · exact hB
  · exfalso
    apply h00
    simpa [hB0] using And.intro hLQ hSQ
  · exfalso
    apply h01
    simpa [hB1] using And.intro hLQ hSQ
  · exfalso
    apply h10
    simpa [hC0] using And.intro hLQ hSQ
  · exfalso
    apply h11
    simpa [hC1] using And.intro hLQ hSQ
  · exfalso
    apply hcc
    simpa [hC] using And.intro hLQ hSQ

/-- Dual-right boundary version used in rank-four local repairs. -/
theorem no_five_alternative_common_pairs_forces_boundary_loop
    (L R : Matroid α) {b₀ b₁ c₀ c₁ : α}
    (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hdisj : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hLE : L.E = ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α))
    (hRE : R.E = ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α))
    (hLB : L.IsBase ({b₀, b₁} : Set α))
    (hRdualB : R✶.IsBase ({b₀, b₁} : Set α))
    (h00 : ¬ (L.IsBase ({b₀, c₀} : Set α) ∧
      R✶.IsBase ({b₀, c₀} : Set α)))
    (h01 : ¬ (L.IsBase ({b₀, c₁} : Set α) ∧
      R✶.IsBase ({b₀, c₁} : Set α)))
    (h10 : ¬ (L.IsBase ({b₁, c₀} : Set α) ∧
      R✶.IsBase ({b₁, c₀} : Set α)))
    (h11 : ¬ (L.IsBase ({b₁, c₁} : Set α) ∧
      R✶.IsBase ({b₁, c₁} : Set α)))
    (hcc : ¬ (L.IsBase ({c₀, c₁} : Set α) ∧
      R✶.IsBase ({c₀, c₁} : Set α))) :
    L.IsLoop c₀ ∨ L.IsLoop c₁ ∨ R.IsLoop b₀ ∨ R.IsLoop b₁ := by
  have hREdual :
      R✶.E = ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α) := by
    simpa using hRE
  have h :=
    no_five_alternative_common_pairs_forces_loop_or_coloop
      L R✶ hb hc hdisj hLE hREdual hLB hRdualB
      h00 h01 h10 h11 hcc
  simpa [Matroid.IsColoop] using h

end LocalRepairFivePairRigidity
end HigherRankKUM
