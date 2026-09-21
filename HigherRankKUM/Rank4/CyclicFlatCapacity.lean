import HigherRankKUM.Rank4.CyclicPigeonhole
import HigherRankKUM.Rank4.CyclicWindowFour

namespace HigherRankKUM
namespace Rank4CyclicFlatCapacity

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- On a cycle of length `4k+1`, if every four consecutive positions hit
`Good`, then there are at least `k+1` good positions.

This is the cyclic packing inequality behind the rank-three capacity
`3k` in a rank-four deletion CBO. -/
theorem ncard_good_ge_k_add_one_of_hits_every_four
    {k : ℕ}
    (Good : Fin (4 * k + 1) → Prop)
    (hHit :
      ∀ i : Fin (4 * k + 1),
        Good i ∨
        Good (cyclicIndex (4 * k + 1) (by omega) i 1) ∨
        Good (cyclicIndex (4 * k + 1) (by omega) i 2) ∨
        Good (cyclicIndex (4 * k + 1) (by omega) i 3)) :
    k + 1 ≤ ({i | Good i} : Set (Fin (4 * k + 1))).ncard := by
  classical
  let n := 4 * k + 1
  let hn : 0 < n := by
    dsimp [n]
    omega
  let shift1 : Fin n → Fin n := fun i => cyclicIndex n hn i 1
  let shift2 : Fin n → Fin n := fun i => cyclicIndex n hn i 2
  let shift3 : Fin n → Fin n := fun i => cyclicIndex n hn i 3
  let G : Set (Fin n) := {i | Good i}
  let A1 : Set (Fin n) := shift1 ⁻¹' G
  let A2 : Set (Fin n) := shift2 ⁻¹' G
  let A3 : Set (Fin n) := shift3 ⁻¹' G

  have hshift1_inj : Function.Injective shift1 := by
    dsimp [shift1]
    exact cyclicIndex_injective_start n hn 1
  have hshift2_inj : Function.Injective shift2 := by
    dsimp [shift2]
    exact cyclicIndex_injective_start n hn 2
  have hshift3_inj : Function.Injective shift3 := by
    dsimp [shift3]
    exact cyclicIndex_injective_start n hn 3
  have hshift1_surj : Function.Surjective shift1 :=
    Finite.surjective_of_injective hshift1_inj
  have hshift2_surj : Function.Surjective shift2 :=
    Finite.surjective_of_injective hshift2_inj
  have hshift3_surj : Function.Surjective shift3 :=
    Finite.surjective_of_injective hshift3_inj

  have hA1card : A1.ncard = G.ncard := by
    dsimp [A1]
    exact Set.ncard_preimage_of_injective_subset_range
      hshift1_inj (fun g hg => hshift1_surj g)
  have hA2card : A2.ncard = G.ncard := by
    dsimp [A2]
    exact Set.ncard_preimage_of_injective_subset_range
      hshift2_inj (fun g hg => hshift2_surj g)
  have hA3card : A3.ncard = G.ncard := by
    dsimp [A3]
    exact Set.ncard_preimage_of_injective_subset_range
      hshift3_inj (fun g hg => hshift3_surj g)

  have hcover :
      (Set.univ : Set (Fin n)) ⊆ ((G ∪ A1) ∪ A2) ∪ A3 := by
    intro i hi
    have h := hHit i
    rcases h with hiG | hi1 | hi2 | hi3
    · exact Or.inl (Or.inl (Or.inl hiG))
    · exact Or.inl (Or.inl (Or.inr hi1))
    · exact Or.inl (Or.inr hi2)
    · exact Or.inr hi3

  have hcardCover :
      (Set.univ : Set (Fin n)).ncard ≤
        (((G ∪ A1) ∪ A2) ∪ A3).ncard :=
    Set.ncard_le_ncard hcover (Set.toFinite _)

  have h01 :
      (G ∪ A1).ncard ≤ G.ncard + A1.ncard :=
    Set.ncard_union_le _ _
  have h012 :
      ((G ∪ A1) ∪ A2).ncard ≤
        (G ∪ A1).ncard + A2.ncard :=
    Set.ncard_union_le _ _
  have h0123 :
      (((G ∪ A1) ∪ A2) ∪ A3).ncard ≤
        ((G ∪ A1) ∪ A2).ncard + A3.ncard :=
    Set.ncard_union_le _ _

  have hUpper :
      (((G ∪ A1) ∪ A2) ∪ A3).ncard ≤ 4 * G.ncard := by
    rw [hA1card] at h01
    rw [hA2card] at h012
    rw [hA3card] at h0123
    omega

  have huniv : (Set.univ : Set (Fin n)).ncard = n := by
    simp
  rw [huniv] at hcardCover
  have htotal : n ≤ 4 * G.ncard :=
    hcardCover.trans hUpper
  dsimp [n, G] at htotal ⊢
  omega

/-- A rank-at-most-three set cannot contain a full rank-four basis window.

Equivalently, along any rank-four cyclic basis ordering, the complement of a
rank-at-most-three set hits every four consecutive positions.  This is the
local window-hitting interface behind all later capacity and saturation
arguments. -/
theorem rankThree_complement_hits_every_four_of_cyclicBasisOrder
    {M : Matroid α} {E H : Set α} {n : ℕ}
    (hn : 0 < n)
    (hRank : M.eRank = (4 : ℕ∞))
    (hHrank : M.eRk H ≤ (3 : ℕ∞))
    (σ : Fin n ≃ E)
    (hCBO : CyclicBasisOrder M 4 hn σ) :
    ∀ i : Fin n,
      (σ i : α) ∉ H ∨
      (σ (cyclicIndex n hn i 1) : α) ∉ H ∨
      (σ (cyclicIndex n hn i 2) : α) ∉ H ∨
      (σ (cyclicIndex n hn i 3) : α) ∉ H := by
  intro i
  by_contra hnone
  push Not at hnone
  have hBsub : cyclicWindow 4 hn σ i ⊆ H := by
    rw [cyclicWindow_four_eq]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx
    · subst x
      exact hnone.1
    · subst x
      exact hnone.2.1
    · subst x
      exact hnone.2.2.1
    · subst x
      exact hnone.2.2.2
  have hmono := M.eRk_mono hBsub
  have hbase := hCBO i
  rw [hbase.eRk_eq_eRank, hRank] at hmono
  have : (4 : ℕ∞) ≤ (3 : ℕ∞) :=
    hmono.trans hHrank
  norm_num at this

/-- A rank-at-most-three subset of a rank-four cyclic basis ordering on
`4k+1` elements contains at most `3k` elements.

Each basis window of length four must contain an element outside the
rank-three set. The preceding cyclic packing lemma then forces at least
`k+1` outside positions. -/
theorem rankThree_ncard_le_three_mul_of_cyclicBasisOrder
    {M : Matroid α} {E H : Set α} {k : ℕ}
    (hE : E.Finite)
    (hEcard : E.ncard = 4 * k + 1)
    (hHsub : H ⊆ E)
    (hRank : M.eRank = (4 : ℕ∞))
    (hHrank : M.eRk H ≤ (3 : ℕ∞))
    (σ : Fin (4 * k + 1) ≃ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    H.ncard ≤ 3 * k := by
  let Good : Fin (4 * k + 1) → Prop :=
    fun i => (σ i : α) ∉ H
  have hHit :
      ∀ i : Fin (4 * k + 1),
        Good i ∨
        Good (cyclicIndex (4 * k + 1) (by omega) i 1) ∨
        Good (cyclicIndex (4 * k + 1) (by omega) i 2) ∨
        Good (cyclicIndex (4 * k + 1) (by omega) i 3) := by
    simpa [Good] using
      (rankThree_complement_hits_every_four_of_cyclicBasisOrder
        (M := M) (H := H) (hn := by omega)
        hRank hHrank σ hCBO)


  have hGood :=
    ncard_good_ge_k_add_one_of_hits_every_four Good hHit
  let G : Set (Fin (4 * k + 1)) := {i | Good i}
  let C : Set α := E \ H
  let f : Fin (4 * k + 1) → α := fun i => (σ i : α)
  have hfInj : Function.Injective f := by
    intro i j hij
    apply σ.injective
    apply Subtype.ext
    exact hij
  have hCrange : C ⊆ Set.range f := by
    intro x hx
    let q : Fin (4 * k + 1) := σ.symm ⟨x, hx.1⟩
    refine ⟨q, ?_⟩
    dsimp [f, q]
    exact congrArg Subtype.val (σ.apply_symm_apply ⟨x, hx.1⟩)
  have hpre : f ⁻¹' C = G := by
    ext i
    simp [f, C, G, Good]
  have hCcard : C.ncard = G.ncard := by
    have h :=
      Set.ncard_preimage_of_injective_subset_range hfInj hCrange
    rw [hpre] at h
    exact h.symm
  have hCge : k + 1 ≤ C.ncard := by
    rw [hCcard]
    simpa [G] using hGood
  have hHfin : H.Finite := hE.subset hHsub
  have hCeq : C.ncard = E.ncard - H.ncard := by
    simpa [C] using Set.ncard_sdiff' hHsub hE
  rw [hCeq, hEcard] at hCge
  omega

end

end Rank4CyclicFlatCapacity
end HigherRankKUM
