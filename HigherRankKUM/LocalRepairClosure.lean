import HigherRankKUM.LocalRepairBoundary

namespace HigherRankKUM
namespace LocalRepairClosure

open Set

variable {α : Type*}

/-- The four-element boundary matroid obtained by contracting an unchanged
interior `C` and then restricting to the four locally moved elements `U`. -/
def boundaryMinor (M : Matroid α) (C U : Set α) : Matroid α :=
  (M.contract C) ↾ U

@[simp]
theorem boundaryMinor_ground (M : Matroid α) (C U : Set α) :
    (boundaryMinor M C U).E = U := rfl

/-- A loop in a restricted contraction is an ambient closure relation, provided
the element really belongs to the contraction ground. -/
theorem mem_closure_of_boundaryMinor_isLoop
    (M : Matroid α) {C U : Set α} {e : α}
    (he : e ∈ (M.contract C).E)
    (hloop : (boundaryMinor M C U).IsLoop e) :
    e ∈ M.closure C := by
  have hr := (Matroid.restrict_isLoop_iff).1 hloop
  rcases hr.2 with hcontract | hout
  · exact (Matroid.contract_isLoop_iff_mem_closure.1 hcontract).1
  · exact (hout he).elim

/-- Ambient-closure form of local repair rigidity.  Let `B={b₀,b₁}` and
`D={c₀,c₁}` be the two current pair blocks and `U=B∪D`.  Form the left and
right local boundary matroids by contracting their unchanged interiors and
restricting to `U`.  If `B` is the unique common base of the left boundary
matroid and the dual of the right boundary matroid, then some moved element is
spanned by the unchanged core on one side.

This is the bridge from the finite four-element rigidity theorem back to the
original matroid. -/
theorem unique_local_repair_forces_ambient_closure
    (M : Matroid α) {CL CR : Set α} {b₀ b₁ c₀ c₁ : α}
    (hb : b₀ ≠ b₁) (hc : c₀ ≠ c₁)
    (hdisj : Disjoint ({b₀, b₁} : Set α) ({c₀, c₁} : Set α))
    (hc₀L : c₀ ∈ (M.contract CL).E)
    (hc₁L : c₁ ∈ (M.contract CL).E)
    (hb₀R : b₀ ∈ (M.contract CR).E)
    (hb₁R : b₁ ∈ (M.contract CR).E)
    (hLB : (boundaryMinor M CL
      (({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α))).IsBase {b₀, b₁})
    (hRdualB : (boundaryMinor M CR
      (({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α)))✶.IsBase {b₀, b₁})
    (hunique : ∀ Q : Set α,
      (boundaryMinor M CL
        (({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α))).IsBase Q →
      (boundaryMinor M CR
        (({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α)))✶.IsBase Q →
      Q = {b₀, b₁}) :
    c₀ ∈ M.closure CL ∨ c₁ ∈ M.closure CL ∨
      b₀ ∈ M.closure CR ∨ b₁ ∈ M.closure CR := by
  let U : Set α := ({b₀, b₁} : Set α) ∪ ({c₀, c₁} : Set α)
  let L := boundaryMinor M CL U
  let R := boundaryMinor M CR U
  have hrigid :
      L.IsLoop c₀ ∨ L.IsLoop c₁ ∨ R.IsLoop b₀ ∨ R.IsLoop b₁ := by
    apply LocalRepairBoundary.unique_common_pair_with_dual_forces_boundary_loop
      L R hb hc hdisj
    · simp [L, U]
    · simp [R, U]
    · simpa [L, U] using hLB
    · simpa [R, U] using hRdualB
    · intro Q hLQ hRQ
      exact hunique Q (by simpa [L, U] using hLQ) (by simpa [R, U] using hRQ)
  rcases hrigid with h | h | h | h
  · exact Or.inl (mem_closure_of_boundaryMinor_isLoop M hc₀L (by simpa [L, U] using h))
  · exact Or.inr (Or.inl
      (mem_closure_of_boundaryMinor_isLoop M hc₁L (by simpa [L, U] using h)))
  · exact Or.inr (Or.inr (Or.inl
      (mem_closure_of_boundaryMinor_isLoop M hb₀R (by simpa [R, U] using h))))
  · exact Or.inr (Or.inr (Or.inr
      (mem_closure_of_boundaryMinor_isLoop M hb₁R (by simpa [R, U] using h))))

end LocalRepairClosure
end HigherRankKUM
