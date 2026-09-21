import HigherRankKUM.LocalRepairClosure
import HigherRankKUM.AdjacentRepair
import HigherRankKUM.Rank4.CyclicWindowFour

namespace HigherRankKUM
namespace Rank4CyclicLocalRepairRigidity

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

private theorem orderValue_ne_of_offset_ne
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (i : Fin n)
    {a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (σ (cyclicIndex n hn i a) : α) ≠
      (σ (cyclicIndex n hn i b) : α) := by
  intro h
  apply hab
  apply cyclicIndex_injective_offsets n hn i ha hb
  apply σ.injective
  apply Subtype.ext
  exact h

private theorem offset_not_mem_first_two
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h8n : 8 ≤ n)
    (σ : Fin n ≃ E) (i : Fin n)
    {a : ℕ} (ha : 2 ≤ a) (ha8 : a < 8) :
    (σ (cyclicIndex n hn i a) : α) ∉ cyclicWindow 2 hn σ i := by
  rw [cyclicWindow_two_eq]
  intro h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · exact (orderValue_ne_of_offset_ne hn σ i
      (a := a) (b := 0) (by omega) (by omega) (by omega)) h
  · exact (orderValue_ne_of_offset_ne hn σ i
      (a := a) (b := 1) (by omega) (by omega) (by omega)) h

private theorem offset_not_mem_last_two
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (h8n : 8 ≤ n)
    (σ : Fin n ≃ E) (i : Fin n)
    {a : ℕ} (ha : a < 6) :
    (σ (cyclicIndex n hn i a) : α) ∉
      cyclicWindow 2 hn σ (cyclicIndex n hn i 6) := by
  rw [cyclicWindow_two_eq]
  simp only [cyclicIndex_add]
  intro h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · exact (orderValue_ne_of_offset_ne hn σ i
      (a := a) (b := 6) (by omega) (by omega) (by omega)) (by simpa using h)
  · exact (orderValue_ne_of_offset_ne hn σ i
      (a := a) (b := 7) (by omega) (by omega) (by omega)) (by simpa using h)

/-- The left two-core together with the first moved pair is exactly the
rank-four CBO window beginning at the local anchor. -/
private theorem left_core_union_pair_eq_window
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow 2 hn σ i ∪
        ({(σ (cyclicIndex n hn i 2) : α),
          (σ (cyclicIndex n hn i 3) : α)} : Set α) =
      cyclicWindow 4 hn σ i := by
  rw [cyclicWindow_two_eq, cyclicWindow_four_eq]
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- The second moved pair together with the right two-core is exactly the
rank-four CBO window beginning four steps after the local anchor. -/
private theorem pair_union_right_core_eq_window
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (i : Fin n) :
    ({(σ (cyclicIndex n hn i 4) : α),
      (σ (cyclicIndex n hn i 5) : α)} : Set α) ∪
        cyclicWindow 2 hn σ (cyclicIndex n hn i 6) =
      cyclicWindow 4 hn σ (cyclicIndex n hn i 4) := by
  rw [cyclicWindow_two_eq, cyclicWindow_four_eq]
  simp only [cyclicIndex_add]
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Local four-block rigidity inside a rank-four CBO.

Use eight consecutive positions:
* offsets 0,1 form the unchanged left core `CL`;
* offsets 2,3 form the current left moved pair `B`;
* offsets 4,5 form the current right moved pair `D`;
* offsets 6,7 form the unchanged right core `CR`.

Contract the two cores and restrict both boundary minors to the four moved
elements.  If `B` is the unique common base of the left boundary minor and
the dual right boundary minor, then one of the opposite pair elements is
spanned by the left core or one of the current-left-pair elements is spanned
by the right core.

This is a completely local version of the old pair-cycle rigidity theorem:
no global pair partition is assumed. -/
theorem unique_four_block_repartition_forces_neighbor_pair_closure
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h8n : 8 ≤ n)
    (σ : Fin n ≃ E)
    (hCBO : CyclicBasisOrder M 4 hn σ)
    (i : Fin n)
    (hunique :
      let b₀ : α := (σ (cyclicIndex n hn i 2) : α)
      let b₁ : α := (σ (cyclicIndex n hn i 3) : α)
      let c₀ : α := (σ (cyclicIndex n hn i 4) : α)
      let c₁ : α := (σ (cyclicIndex n hn i 5) : α)
      let CL := cyclicWindow 2 hn σ i
      let CR := cyclicWindow 2 hn σ (cyclicIndex n hn i 6)
      let U : Set α := ({b₀,b₁} : Set α) ∪ ({c₀,c₁} : Set α)
      ∀ Q : Set α,
        (LocalRepairClosure.boundaryMinor M CL U).IsBase Q →
        (LocalRepairClosure.boundaryMinor M CR U)✶.IsBase Q →
        Q = {b₀,b₁}) :
    let b₀ : α := (σ (cyclicIndex n hn i 2) : α)
    let b₁ : α := (σ (cyclicIndex n hn i 3) : α)
    let c₀ : α := (σ (cyclicIndex n hn i 4) : α)
    let c₁ : α := (σ (cyclicIndex n hn i 5) : α)
    let CL := cyclicWindow 2 hn σ i
    let CR := cyclicWindow 2 hn σ (cyclicIndex n hn i 6)
    c₀ ∈ M.closure CL ∨ c₁ ∈ M.closure CL ∨
      b₀ ∈ M.closure CR ∨ b₁ ∈ M.closure CR := by
  dsimp at hunique ⊢
  let b₀ : α := (σ (cyclicIndex n hn i 2) : α)
  let b₁ : α := (σ (cyclicIndex n hn i 3) : α)
  let c₀ : α := (σ (cyclicIndex n hn i 4) : α)
  let c₁ : α := (σ (cyclicIndex n hn i 5) : α)
  let CL := cyclicWindow 2 hn σ i
  let CR := cyclicWindow 2 hn σ (cyclicIndex n hn i 6)
  let B : Set α := {b₀,b₁}
  let D : Set α := {c₀,c₁}
  let U : Set α := B ∪ D

  have hb : b₀ ≠ b₁ := by
    dsimp [b₀,b₁]
    exact orderValue_ne_of_offset_ne hn σ i
      (by omega) (by omega) (by omega)
  have hc : c₀ ≠ c₁ := by
    dsimp [c₀,c₁]
    exact orderValue_ne_of_offset_ne hn σ i
      (by omega) (by omega) (by omega)
  have hdisj : Disjoint B D := by
    rw [Set.disjoint_left]
    intro x hxB hxD
    simp only [B,D, Set.mem_insert_iff, Set.mem_singleton_iff] at hxB hxD
    rcases hxB with rfl | rfl <;> rcases hxD with h | h
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 2) (b := 4) (by omega) (by omega) (by omega)) h
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 2) (b := 5) (by omega) (by omega) (by omega)) h
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 3) (b := 4) (by omega) (by omega) (by omega)) h
    · exact (orderValue_ne_of_offset_ne hn σ i
        (a := 3) (b := 5) (by omega) (by omega) (by omega)) h

  have hCLsub : CL ⊆ cyclicWindow 4 hn σ i := by
    dsimp [CL]
    rw [cyclicWindow_two_eq, cyclicWindow_four_eq]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
  have hCRsub :
      CR ⊆ cyclicWindow 4 hn σ (cyclicIndex n hn i 4) := by
    dsimp [CR]
    rw [cyclicWindow_two_eq, cyclicWindow_four_eq]
    simp only [cyclicIndex_add]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inr (Or.inr (Or.inl (by simpa using hx)))
    · exact Or.inr (Or.inr (Or.inr (by simpa using hx)))

  have hCLind : M.Indep CL := (hCBO i).indep.subset hCLsub
  have hCRind : M.Indep CR :=
    (hCBO (cyclicIndex n hn i 4)).indep.subset hCRsub

  have hBCL : Disjoint B CL := by
    rw [Set.disjoint_left]
    intro x hxB hxCL
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at hxB
    rcases hxB with rfl | rfl
    · exact offset_not_mem_first_two hn h8n σ i (a := 2) (by omega) (by omega) hxCL
    · exact offset_not_mem_first_two hn h8n σ i (a := 3) (by omega) (by omega) hxCL
  have hDCR : Disjoint D CR := by
    rw [Set.disjoint_left]
    intro x hxD hxCR
    simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hxD
    rcases hxD with rfl | rfl
    · exact offset_not_mem_last_two hn h8n σ i (a := 4) (by omega) hxCR
    · exact offset_not_mem_last_two hn h8n σ i (a := 5) (by omega) hxCR

  have hBbaseAmbient : M.IsBase (B ∪ CL) := by
    rw [Set.union_comm]
    simpa [B,b₀,b₁] using
      (show M.IsBase (cyclicWindow 4 hn σ i) from hCBO i)
      |> fun h => by
        rw [← left_core_union_pair_eq_window hn σ i]
        exact h
  have hDbaseAmbient : M.IsBase (D ∪ CR) := by
    simpa [D,c₀,c₁] using
      (show M.IsBase (cyclicWindow 4 hn σ (cyclicIndex n hn i 4)) from
        hCBO (cyclicIndex n hn i 4))
      |> fun h => by
        rw [← pair_union_right_core_eq_window hn σ i]
        exact h

  have hBcontract : (M.contract CL).IsBase B :=
    hCLind.contract_isBase_iff.2 ⟨hBbaseAmbient, hBCL⟩
  have hDcontract : (M.contract CR).IsBase D :=
    hCRind.contract_isBase_iff.2 ⟨hDbaseAmbient, hDCR⟩

  have hc₀L : c₀ ∈ (M.contract CL).E := by
    rw [Matroid.contract_ground]
    refine ⟨(σ (cyclicIndex n hn i 4)).property, ?_⟩
    exact offset_not_mem_first_two hn h8n σ i (a := 4) (by omega) (by omega)
  have hc₁L : c₁ ∈ (M.contract CL).E := by
    rw [Matroid.contract_ground]
    refine ⟨(σ (cyclicIndex n hn i 5)).property, ?_⟩
    exact offset_not_mem_first_two hn h8n σ i (a := 5) (by omega) (by omega)
  have hb₀R : b₀ ∈ (M.contract CR).E := by
    rw [Matroid.contract_ground]
    refine ⟨(σ (cyclicIndex n hn i 2)).property, ?_⟩
    exact offset_not_mem_last_two hn h8n σ i (a := 2) (by omega)
  have hb₁R : b₁ ∈ (M.contract CR).E := by
    rw [Matroid.contract_ground]
    refine ⟨(σ (cyclicIndex n hn i 3)).property, ?_⟩
    exact offset_not_mem_last_two hn h8n σ i (a := 3) (by omega)

  have hUleft : U ⊆ (M.contract CL).E := by
    intro x hx
    rcases hx with hxB | hxD
    · exact hBcontract.subset_ground hxB
    · simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hxD
      rcases hxD with rfl | rfl
      · exact hc₀L
      · exact hc₁L
  have hUright : U ⊆ (M.contract CR).E := by
    intro x hx
    rcases hx with hxB | hxD
    · simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at hxB
      rcases hxB with rfl | rfl
      · exact hb₀R
      · exact hb₁R
    · exact hDcontract.subset_ground hxD

  have hLB :
      (LocalRepairClosure.boundaryMinor M CL U).IsBase B := by
    rw [LocalRepairClosure.boundaryMinor,
      Matroid.isBase_restrict_iff hUleft]
    apply hBcontract.isBasis_of_subset (hX := hUleft)
    exact Set.subset_union_left

  have hRD :
      (LocalRepairClosure.boundaryMinor M CR U).IsBase D := by
    rw [LocalRepairClosure.boundaryMinor,
      Matroid.isBase_restrict_iff hUright]
    apply hDcontract.isBasis_of_subset (hX := hUright)
    exact Set.subset_union_right

  have hBsubU : B ⊆ U := Set.subset_union_left
  have hUdiffB : U \ B = D := by
    ext x
    constructor
    · rintro ⟨hxU,hxnot⟩
      rcases hxU with hxB | hxD
      · exact (hxnot hxB).elim
      · exact hxD
    · intro hxD
      refine ⟨Or.inr hxD, ?_⟩
      intro hxB
      exact Set.disjoint_left.1 hdisj hxB hxD
  have hRdualB :
      (LocalRepairClosure.boundaryMinor M CR U)✶.IsBase B := by
    apply (AdjacentRepair.complement_isBase_iff_dual_isBase
      (LocalRepairClosure.boundaryMinor M CR U)
      (by simp [LocalRepairClosure.boundaryMinor]) hBsubU).1
    rw [hUdiffB]
    exact hRD

  have h :=
    LocalRepairClosure.unique_local_repair_forces_ambient_closure
      M hb hc hdisj hc₀L hc₁L hb₀R hb₁R hLB hRdualB
      (by
        intro Q hLQ hRQ
        simpa [B,b₀,b₁,D,c₀,c₁,CL,CR,U] using
          hunique Q
            (by simpa [B,D,U,CL,CR,b₀,b₁,c₀,c₁] using hLQ)
            (by simpa [B,D,U,CL,CR,b₀,b₁,c₀,c₁] using hRQ))
  simpa [b₀,b₁,c₀,c₁,CL,CR] using h

end

end Rank4CyclicLocalRepairRigidity
end HigherRankKUM
