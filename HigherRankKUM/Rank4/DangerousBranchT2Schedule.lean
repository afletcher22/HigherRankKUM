import HigherRankKUM.Rank4.DangerousBranchFactors
import HigherRankKUM.Rank4.DangerousBranchT2Good
import HigherRankKUM.Rank4.CyclicPigeonhole
import HigherRankKUM.CyclicRotation

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

/-- Along any cyclic basis ordering of the rank-two core, one can find an
oriented adjacent core edge whose tail is good for the B-side and whose head
is good for the A-side. -/
theorem dangerous_two_exists_oriented_good_core_edge
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 1 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K)
    (order : Fin (2 * k) ≃ (M.restrict (H ∩ K)).E)
    (hOrder : CyclicBasisOrder (M.restrict (H ∩ K)) 2 (by omega) order) :
    ∃ j : Fin (2 * k),
      ∃ b₀ b₁ a₀ a₁ : α,
        b₀ ∈ M.E \ K ∧ b₁ ∈ M.E \ K ∧ b₀ ≠ b₁ ∧
        a₀ ∈ M.E \ H ∧ a₁ ∈ M.E \ H ∧ a₀ ≠ a₁ ∧
        M.IsBasis ({(order j : α), b₀, b₁} : Set α) H ∧
        M.IsBasis
          ({(order (cyclicIndex (2 * k) (by omega) j 1) : α), a₀, a₁} : Set α)
          K := by
  obtain ⟨BadA, hBadAsub, hBadAcard, hGoodA⟩ :=
    dangerous_two_exists_small_bad_set
      hk hE hRank hEcard hStrict hH hK hne
  obtain ⟨BadB, hBadBsub, hBadBcard, hGoodB⟩ :=
    dangerous_two_exists_small_bad_set
      hk hE hRank hEcard hStrict hK hH hne.symm

  let f : Fin (2 * k) → α := fun i => (order i : α)
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply order.injective
    exact Subtype.ext hij

  have hcoreMem (i : Fin (2 * k)) : f i ∈ H ∩ K := by
    have hi := (order i).property
    simpa [f] using hi

  have hBadA_range : BadA ⊆ Set.range f := by
    intro x hx
    have hxG : x ∈ H ∩ K := hBadAsub hx
    have hxE : x ∈ M.E := hH.subset_ground hxG.1
    let sx : (M.restrict (H ∩ K)).E := ⟨x, by
      simpa using And.intro hxG hxE⟩
    refine ⟨order.symm sx, ?_⟩
    dsimp [f, sx]
    simpa using congrArg Subtype.val (order.apply_symm_apply sx)

  have hBadB_range : BadB ⊆ Set.range f := by
    intro x hx
    have hxG' : x ∈ K ∩ H := hBadBsub hx
    have hxG : x ∈ H ∩ K := by simpa [Set.inter_comm] using hxG'
    have hxE : x ∈ M.E := hH.subset_ground hxG.1
    let sx : (M.restrict (H ∩ K)).E := ⟨x, by
      simpa using And.intro hxG hxE⟩
    refine ⟨order.symm sx, ?_⟩
    dsimp [f, sx]
    simpa using congrArg Subtype.val (order.apply_symm_apply sx)

  let Aidx : Set (Fin (2 * k)) := f ⁻¹' BadA
  let Bidx : Set (Fin (2 * k)) := f ⁻¹' BadB
  have hAidxCard : Aidx.ncard = BadA.ncard := by
    dsimp [Aidx]
    exact Set.ncard_preimage_of_injective_subset_range hf_inj hBadA_range
  have hBidxCard : Bidx.ncard = BadB.ncard := by
    dsimp [Bidx]
    exact Set.ncard_preimage_of_injective_subset_range hf_inj hBadB_range
  have hAidxLe : Aidx.ncard ≤ k - 1 := by
    rw [hAidxCard]
    exact hBadAcard
  have hBidxLe : Bidx.ncard ≤ k - 1 := by
    rw [hBidxCard]
    exact hBadBcard

  obtain ⟨j, hjB, hjA⟩ :=
    exists_cyclic_edge_avoiding_two_small_sets hk Bidx Aidx hBidxLe hAidxLe

  have hjB' : f j ∉ BadB := by
    simpa [Bidx] using hjB
  have hjA' :
      f (cyclicIndex (2 * k) (by omega) j 1) ∉ BadA := by
    simpa [Aidx] using hjA

  have hjCore : f j ∈ K ∩ H := by
    simpa [Set.inter_comm] using hcoreMem j
  have hjNextCore :
      f (cyclicIndex (2 * k) (by omega) j 1) ∈ H ∩ K :=
    hcoreMem _

  obtain ⟨b₀, b₁, hb₀, hb₁, hbne, hbBasis⟩ :=
    hGoodB (f j) hjCore hjB'
  obtain ⟨a₀, a₁, ha₀, ha₁, hane, haBasis⟩ :=
    hGoodA (f (cyclicIndex (2 * k) (by omega) j 1)) hjNextCore hjA'

  refine ⟨j, b₀, b₁, a₀, a₁, hb₀, hb₁, hbne, ha₀, ha₁, hane, ?_, ?_⟩
  · simpa [f] using hbBasis
  · simpa [f] using haBasis


/-- Rotate a cyclic order so a chosen oriented adjacent edge occupies the last
two positions. -/
theorem exists_shifted_order_with_edge_at_end
    {E : Set α} {k : ℕ}
    (hk : 1 ≤ k)
    (order : Fin (2 * k) ≃ E)
    (j : Fin (2 * k)) :
    ∃ order' : Fin (2 * k) ≃ E,
      (order' ⟨2 * k - 2, by omega⟩ : α) = (order j : α) ∧
      (order' ⟨2 * k - 1, by omega⟩ : α) =
        (order (cyclicIndex (2 * k) (by omega) j 1) : α) := by
  let hn : 0 < 2 * k := by omega
  let i0 : Fin (2 * k) := ⟨2 * k - 2, by omega⟩
  let i1 : Fin (2 * k) := ⟨2 * k - 1, by omega⟩
  obtain ⟨t, ht, _⟩ :=
    existsUnique_cyclicIndex_offset (2 * k) hn i0 j
  let order' : Fin (2 * k) ≃ E :=
    (cyclicShiftEquiv (2 * k) hn t.val).trans order
  refine ⟨order', ?_, ?_⟩
  · change
      (order
        (cyclicShiftEquiv (2 * k) hn t.val i0) : α) =
        (order j : α)
    rw [cyclicShiftEquiv_apply, ← ht]
  · have hi1 :
        i1 = cyclicIndex (2 * k) hn i0 1 := by
      apply Fin.ext
      simp [i0, i1, cyclicIndex]
      omega
    change
      (order
        (cyclicShiftEquiv (2 * k) hn t.val i1) : α) =
        (order (cyclicIndex (2 * k) hn j 1) : α)
    rw [hi1, cyclicShiftEquiv_cyclicIndex, cyclicShiftEquiv_apply, ← ht]

/-- The same rotation preserves a core cyclic basis ordering. -/
theorem exists_shifted_core_cbo_with_edge_at_end
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 1 ≤ k)
    (order : Fin (2 * k) ≃ (M.restrict (H ∩ K)).E)
    (hOrder : CyclicBasisOrder (M.restrict (H ∩ K)) 2 (by omega) order)
    (j : Fin (2 * k)) :
    ∃ order' : Fin (2 * k) ≃ (M.restrict (H ∩ K)).E,
      CyclicBasisOrder (M.restrict (H ∩ K)) 2 (by omega) order' ∧
      (order' ⟨2 * k - 2, by omega⟩ : α) = (order j : α) ∧
      (order' ⟨2 * k - 1, by omega⟩ : α) =
        (order (cyclicIndex (2 * k) (by omega) j 1) : α) := by
  let hn : 0 < 2 * k := by omega
  let i0 : Fin (2 * k) := ⟨2 * k - 2, by omega⟩
  obtain ⟨t, ht, _⟩ :=
    existsUnique_cyclicIndex_offset (2 * k) hn i0 j
  let order' : Fin (2 * k) ≃ (M.restrict (H ∩ K)).E :=
    (cyclicShiftEquiv (2 * k) hn t.val).trans order
  have hCBO :
      CyclicBasisOrder (M.restrict (H ∩ K)) 2 hn order' := by
    exact hOrder.shift hn order t.val
  refine ⟨order', hCBO, ?_, ?_⟩
  · change
      (order
        (cyclicShiftEquiv (2 * k) hn t.val i0) : α) =
        (order j : α)
    rw [cyclicShiftEquiv_apply, ← ht]
  · let i1 : Fin (2 * k) := ⟨2 * k - 1, by omega⟩
    have hi1 :
        i1 = cyclicIndex (2 * k) hn i0 1 := by
      apply Fin.ext
      simp [i0, i1, cyclicIndex]
      omega
    change
      (order
        (cyclicShiftEquiv (2 * k) hn t.val i1) : α) =
        (order (cyclicIndex (2 * k) hn j 1) : α)
    rw [hi1, cyclicShiftEquiv_cyclicIndex, cyclicShiftEquiv_apply, ← ht]

end

end Rank4DangerousBranches
end HigherRankKUM
