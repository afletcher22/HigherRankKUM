import HigherRankKUM.Rank4.DangerousBranchFactors
import HigherRankKUM.Rank4.DangerousBranchT2Good
import HigherRankKUM.Rank4.CyclicPigeonhole
import HigherRankKUM.CyclicRotation
import HigherRankKUM.Rank4.CyclicWindowFour
import HigherRankKUM.Rank4.CyclicIndexArithmetic

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



/-- Consecutive entries of a rank-two core CBO are independent in the
ambient matroid. -/
theorem dangerous_two_core_order_adjacent_indep
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 1 ≤ k)
    (order : Fin (2 * k) ≃ (M.restrict (H ∩ K)).E)
    (hOrder : CyclicBasisOrder (M.restrict (H ∩ K)) 2 (by omega) order)
    (j : Fin (2 * k)) :
    M.Indep
      ({(order j : α),
        (order (cyclicIndex (2 * k) (by omega) j 1) : α)} : Set α) := by
  have hB := hOrder j
  rw [cyclicWindow_two_eq] at hB
  exact hB.indep.of_restrict

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



/-- Every window starting before the six-element tail of the normalized t=2
schedule is ordinary. The prefix follows A,B,G,G, where the G entries are a
rank-two core CBO in their natural order. -/
theorem dangerous_two_ordinary_prefix_windows
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K)
    (σ : Fin (4 * k + 2) ≃ M.E)
    (order : Fin (2 * k) ≃ (M.restrict (H ∩ K)).E)
    (hOrder : CyclicBasisOrder (M.restrict (H ∩ K)) 2 (by omega) order)
    (hA : ∀ j : Fin k,
      (σ ⟨4 * j.val, by omega⟩ : α) ∈ M.E \ H)
    (hB : ∀ j : Fin k,
      (σ ⟨4 * j.val + 1, by omega⟩ : α) ∈ M.E \ K)
    (hG0 : ∀ j : Fin k,
      (σ ⟨4 * j.val + 2, by omega⟩ : α) =
        (order ⟨2 * j.val, by omega⟩ : α))
    (hG1 : ∀ j : Fin (k - 1),
      (σ ⟨4 * j.val + 3, by omega⟩ : α) =
        (order ⟨2 * j.val + 1, by omega⟩ : α)) :
    let hn : 0 < 4 * k + 2 := by omega
    ∀ i : Fin (4 * k + 2), i.val < 4 * (k - 1) →
      M.IsBase (cyclicWindow 4 hn σ i) := by
  let hn : 0 < 4 * k + 2 := by omega
  intro i hi
  have hi3 : i.val + 3 < 4 * k + 2 := by omega
  let i1 : Fin (4 * k + 2) := ⟨i.val + 1, by omega⟩
  let i2 : Fin (4 * k + 2) := ⟨i.val + 2, by omega⟩
  let i3 : Fin (4 * k + 2) := ⟨i.val + 3, by omega⟩
  have hcy1 : cyclicIndex (4 * k + 2) hn i 1 = i1 := by
    simpa [i1] using cyclicIndex_eq_mk_add_of_lt
      (4 * k + 2) hn i 1 (by omega)
  have hcy2 : cyclicIndex (4 * k + 2) hn i 2 = i2 := by
    simpa [i2] using cyclicIndex_eq_mk_add_of_lt
      (4 * k + 2) hn i 2 (by omega)
  have hcy3 : cyclicIndex (4 * k + 2) hn i 3 = i3 := by
    simpa [i3] using cyclicIndex_eq_mk_add_of_lt
      (4 * k + 2) hn i 3 hi3
  rw [cyclicWindow_four_eq, hcy1, hcy2, hcy3]

  let j : Fin (k - 1) := ⟨i.val / 4, by omega⟩
  have hmod : i.val % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases hr : i.val % 4
  · have hival : i.val = 4 * j.val := by
      dsimp [j]
      have hm := Nat.mod_add_div i.val 4
      omega
    let jk : Fin k := ⟨j.val, by omega⟩
    let g : Fin (2 * k) := ⟨2 * j.val, by omega⟩
    have hnext :
        cyclicIndex (2 * k) (by omega) g 1 =
          ⟨2 * j.val + 1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hpair := dangerous_two_core_order_adjacent_indep
      (M := M) (k := k) (H := H) (K := K)
      (by omega : 1 ≤ k) order hOrder g
    rw [hnext] at hpair
    have hbase := dangerous_two_core_pair_sides_isBase
      (M := M) (k := k) (H₀ := H) (H₁ := K)
      (g₀ := (order ⟨2 * j.val, by omega⟩ : α))
      (g₁ := (order ⟨2 * j.val + 1, by omega⟩ : α))
      (a := (σ i : α)) (b := (σ i1 : α))
      (by omega : 1 ≤ k) hE hRank hEcard hStrict hH hK hne
      (by simpa using (order ⟨2 * j.val, by omega⟩).property)
      (by simpa using (order ⟨2 * j.val + 1, by omega⟩).property)
      (by
        intro hEq
        apply order.injective
        apply Subtype.ext
        exact hEq)
      hpair
      (by simpa [i1, jk, hival] using hA jk)
      (by simpa [i1, jk, hival] using hB jk)
    rw [hival]
    have hg0 := hG0 jk
    have hg1 := hG1 j
    simpa [i1, i2, i3, jk, hival, hg0, hg1,
      Set.pair_comm, or_comm, or_left_comm, or_assoc] using hbase
  · have hival : i.val = 4 * j.val + 1 := by
      dsimp [j]
      have hm := Nat.mod_add_div i.val 4
      omega
    let jk : Fin k := ⟨j.val, by omega⟩
    let jnext : Fin k := ⟨j.val + 1, by omega⟩
    let g : Fin (2 * k) := ⟨2 * j.val, by omega⟩
    have hnext :
        cyclicIndex (2 * k) (by omega) g 1 =
          ⟨2 * j.val + 1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hpair := dangerous_two_core_order_adjacent_indep
      (M := M) (k := k) (H := H) (K := K)
      (by omega : 1 ≤ k) order hOrder g
    rw [hnext] at hpair
    have hbase := dangerous_two_core_pair_sides_isBase
      (M := M) (k := k) (H₀ := H) (H₁ := K)
      (g₀ := (order ⟨2 * j.val, by omega⟩ : α))
      (g₁ := (order ⟨2 * j.val + 1, by omega⟩ : α))
      (a := (σ i3 : α)) (b := (σ i : α))
      (by omega : 1 ≤ k) hE hRank hEcard hStrict hH hK hne
      (by simpa using (order ⟨2 * j.val, by omega⟩).property)
      (by simpa using (order ⟨2 * j.val + 1, by omega⟩).property)
      (by
        intro hEq
        apply order.injective
        apply Subtype.ext
        exact hEq)
      hpair
      (by simpa [i3, jnext, hival] using hA jnext)
      (by simpa [i, jk, hival] using hB jk)
    have hg0 := hG0 jk
    have hg1 := hG1 j
    simpa [i1, i2, i3, jk, jnext, hival, hg0, hg1,
      Set.pair_comm, or_comm, or_left_comm, or_assoc] using hbase
  · have hival : i.val = 4 * j.val + 2 := by
      dsimp [j]
      have hm := Nat.mod_add_div i.val 4
      omega
    let jnext : Fin k := ⟨j.val + 1, by omega⟩
    let jk : Fin k := ⟨j.val, by omega⟩
    let g : Fin (2 * k) := ⟨2 * j.val, by omega⟩
    have hnext :
        cyclicIndex (2 * k) (by omega) g 1 =
          ⟨2 * j.val + 1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hpair := dangerous_two_core_order_adjacent_indep
      (M := M) (k := k) (H := H) (K := K)
      (by omega : 1 ≤ k) order hOrder g
    rw [hnext] at hpair
    have hbase := dangerous_two_core_pair_sides_isBase
      (M := M) (k := k) (H₀ := H) (H₁ := K)
      (g₀ := (order ⟨2 * j.val, by omega⟩ : α))
      (g₁ := (order ⟨2 * j.val + 1, by omega⟩ : α))
      (a := (σ i2 : α)) (b := (σ i3 : α))
      (by omega : 1 ≤ k) hE hRank hEcard hStrict hH hK hne
      (by simpa using (order ⟨2 * j.val, by omega⟩).property)
      (by simpa using (order ⟨2 * j.val + 1, by omega⟩).property)
      (by
        intro hEq
        apply order.injective
        apply Subtype.ext
        exact hEq)
      hpair
      (by simpa [i2, jnext, hival] using hA jnext)
      (by simpa [i3, jnext, hival] using hB jnext)
    have hg0 := hG0 jk
    have hg1 := hG1 j
    simpa [i1, i2, i3, jk, jnext, hival, hg0, hg1,
      Set.pair_comm, or_comm, or_left_comm, or_assoc] using hbase
  · have hival : i.val = 4 * j.val + 3 := by
      dsimp [j]
      have hm := Nat.mod_add_div i.val 4
      omega
    let jnext : Fin k := ⟨j.val + 1, by omega⟩
    let g : Fin (2 * k) := ⟨2 * j.val + 1, by omega⟩
    have hnext :
        cyclicIndex (2 * k) (by omega) g 1 =
          ⟨2 * (j.val + 1), by omega⟩ := by
      apply Fin.ext
      have h := cyclicIndex_eq_mk_add_of_lt
        (2 * k) (by omega) g 1 (by omega)
      simpa [g] using congrArg Fin.val h
    have hpair := dangerous_two_core_order_adjacent_indep
      (M := M) (k := k) (H := H) (K := K)
      (by omega : 1 ≤ k) order hOrder g
    rw [hnext] at hpair
    have hbase := dangerous_two_core_pair_sides_isBase
      (M := M) (k := k) (H₀ := H) (H₁ := K)
      (g₀ := (order ⟨2 * j.val + 1, by omega⟩ : α))
      (g₁ := (order ⟨2 * (j.val + 1), by omega⟩ : α))
      (a := (σ i1 : α)) (b := (σ i2 : α))
      (by omega : 1 ≤ k) hE hRank hEcard hStrict hH hK hne
      (by simpa using (order ⟨2 * j.val + 1, by omega⟩).property)
      (by simpa using (order ⟨2 * (j.val + 1), by omega⟩).property)
      (by
        intro hEq
        apply order.injective
        apply Subtype.ext
        exact hEq)
      hpair
      (by simpa [i1, jnext, hival] using hA jnext)
      (by simpa [i2, jnext, hival] using hB jnext)
    have hg1 := hG1 j
    have hg0 := hG0 jnext
    simpa [i1, i2, i3, jnext, hival, hg0, hg1,
      Set.pair_comm, or_comm, or_left_comm, or_assoc] using hbase

/-- The six exceptional windows of the normalized t=2 schedule are bases.

The tail is
  pA, pB, gB, dB, dA, gA
and the wrapped prefix begins
  qA, qB, g0.
The B-good triple is {gB,pB,dB}; the A-good triple is
{gA,dA,qA}. The remaining two exceptional windows use adjacent core pairs. -/
theorem dangerous_two_six_exceptional_windows
    {M : Matroid α} {k : ℕ} {H K : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K)
    (σ : Fin (4 * k + 2) ≃ M.E)
    {qA pA dA qB pB dB g0 gB gA : α}
    (hqA : qA ∈ M.E \ H) (hpA : pA ∈ M.E \ H) (hdA : dA ∈ M.E \ H)
    (hqB : qB ∈ M.E \ K) (hpB : pB ∈ M.E \ K) (hdB : dB ∈ M.E \ K)
    (hg0 : g0 ∈ H ∩ K) (hgB : gB ∈ H ∩ K) (hgA : gA ∈ H ∩ K)
    (hgBneA : gB ≠ gA) (hgAne0 : gA ≠ g0)
    (hpairBA : M.Indep ({gB, gA} : Set α))
    (hpairA0 : M.Indep ({gA, g0} : Set α))
    (hbBasis : M.IsBasis ({gB, pB, dB} : Set α) H)
    (haBasis : M.IsBasis ({gA, dA, qA} : Set α) K)
    (hσ0 : (σ ⟨0, by omega⟩ : α) = qA)
    (hσ1 : (σ ⟨1, by omega⟩ : α) = qB)
    (hσ2 : (σ ⟨2, by omega⟩ : α) = g0)
    (hσpA : (σ ⟨4 * (k - 1), by omega⟩ : α) = pA)
    (hσpB : (σ ⟨4 * (k - 1) + 1, by omega⟩ : α) = pB)
    (hσgB : (σ ⟨4 * (k - 1) + 2, by omega⟩ : α) = gB)
    (hσdB : (σ ⟨4 * (k - 1) + 3, by omega⟩ : α) = dB)
    (hσdA : (σ ⟨4 * (k - 1) + 4, by omega⟩ : α) = dA)
    (hσgA : (σ ⟨4 * (k - 1) + 5, by omega⟩ : α) = gA) :
    let hn : 0 < 4 * k + 2 := by omega
    M.IsBase (cyclicWindow 4 hn σ ⟨4 * (k - 1), by omega⟩) ∧
    M.IsBase (cyclicWindow 4 hn σ ⟨4 * (k - 1) + 1, by omega⟩) ∧
    M.IsBase (cyclicWindow 4 hn σ ⟨4 * (k - 1) + 2, by omega⟩) ∧
    M.IsBase (cyclicWindow 4 hn σ ⟨4 * (k - 1) + 3, by omega⟩) ∧
    M.IsBase (cyclicWindow 4 hn σ ⟨4 * (k - 1) + 4, by omega⟩) ∧
    M.IsBase (cyclicWindow 4 hn σ ⟨4 * (k - 1) + 5, by omega⟩) := by
  let hn : 0 < 4 * k + 2 := by omega
  let n := 4 * k + 2
  let m := 4 * (k - 1)
  have hmn : m + 6 = n := by
    dsimp [m, n]
    omega
  have hnpos : 0 < n := by simpa [n] using hn

  have hidx (r s : ℕ) (hrs : r + s < 6) :
      cyclicIndex n hnpos ⟨m + r, by omega⟩ s =
        ⟨m + r + s, by omega⟩ := by
    apply cyclicIndex_eq_mk_add_of_lt
    omega

  have hwrap (r s : ℕ) (hr : r < 6) (hge : 6 ≤ r + s)
      (hlt : r + s < 12) :
      cyclicIndex n hnpos ⟨m + r, by omega⟩ s =
        ⟨r + s - 6, by omega⟩ := by
    have h := cyclicIndex_eq_mk_sub_of_ge_of_lt_two_mul
      n hnpos ⟨m + r, by omega⟩ s (by omega) (by omega)
    apply Fin.ext
    simpa [hmn] using congrArg Fin.val h

  have hbase0 : M.IsBase ({pA, pB, gB, dB} : Set α) := by
    have h := dangerous_two_hyperplane_triple_plus_other_isBase
      (M := M) (k := k) (H₀ := H) (H₁ := K)
      (I := ({gB, pB, dB} : Set α)) (a := pA)
      hRank hH hbBasis hpA
    convert h using 1 <;> ext z <;>
      simp [Set.mem_insert_iff, or_comm, or_left_comm, or_assoc]

  have hbase1 : M.IsBase ({pB, gB, dB, dA} : Set α) := by
    have h := dangerous_two_hyperplane_triple_plus_other_isBase
      (M := M) (k := k) (H₀ := H) (H₁ := K)
      (I := ({gB, pB, dB} : Set α)) (a := dA)
      hRank hH hbBasis hdA
    convert h using 1 <;> ext z <;>
      simp [Set.mem_insert_iff, or_comm, or_left_comm, or_assoc]

  have hbase2 : M.IsBase ({gB, dB, dA, gA} : Set α) := by
    have h := dangerous_two_core_pair_sides_isBase
      (M := M) (k := k) (H₀ := H) (H₁ := K)
      (g₀ := gB) (g₁ := gA) (a := dA) (b := dB)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict hH hK hne
      hgB hgA hgBneA hpairBA hdA hdB
    convert h using 1 <;> ext z <;>
      simp [Set.mem_insert_iff, or_comm, or_left_comm, or_assoc]

  have hbase3 : M.IsBase ({dB, dA, gA, qA} : Set α) := by
    have h := dangerous_two_hyperplane_triple_plus_other_isBase
      (M := M) (k := k) (H₀ := K) (H₁ := H)
      (I := ({gA, dA, qA} : Set α)) (a := dB)
      hRank hK haBasis hdB
    convert h using 1 <;> ext z <;>
      simp [Set.mem_insert_iff, or_comm, or_left_comm, or_assoc]

  have hbase4 : M.IsBase ({dA, gA, qA, qB} : Set α) := by
    have h := dangerous_two_hyperplane_triple_plus_other_isBase
      (M := M) (k := k) (H₀ := K) (H₁ := H)
      (I := ({gA, dA, qA} : Set α)) (a := qB)
      hRank hK haBasis hqB
    convert h using 1 <;> ext z <;>
      simp [Set.mem_insert_iff, or_comm, or_left_comm, or_assoc]

  have hbase5 : M.IsBase ({gA, qA, qB, g0} : Set α) := by
    have h := dangerous_two_core_pair_sides_isBase
      (M := M) (k := k) (H₀ := H) (H₁ := K)
      (g₀ := gA) (g₁ := g0) (a := qA) (b := qB)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict hH hK hne
      hgA hg0 hgAne0 hpairA0 hqA hqB
    convert h using 1 <;> ext z <;>
      simp [Set.mem_insert_iff, or_comm, or_left_comm, or_assoc]

  dsimp only
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 0 1 (by omega)
    have h1 := hidx 0 2 (by omega)
    have h2 := hidx 0 3 (by omega)
    simpa [n, m, hn, h0, h1, h2, hσpA, hσpB, hσgB, hσdB] using hbase0
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 1 1 (by omega)
    have h1 := hidx 1 2 (by omega)
    have h2 := hidx 1 3 (by omega)
    simpa [n, m, hn, h0, h1, h2, hσpB, hσgB, hσdB, hσdA] using hbase1
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 2 1 (by omega)
    have h1 := hidx 2 2 (by omega)
    have h2 := hidx 2 3 (by omega)
    simpa [n, m, hn, h0, h1, h2, hσgB, hσdB, hσdA, hσgA] using hbase2
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 3 1 (by omega)
    have h1 := hidx 3 2 (by omega)
    have h2 := hwrap 3 3 (by omega) (by omega) (by omega)
    simpa [n, m, hn, h0, h1, h2, hσdB, hσdA, hσgA, hσ0] using hbase3
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 4 1 (by omega)
    have h1 := hwrap 4 2 (by omega) (by omega) (by omega)
    have h2 := hwrap 4 3 (by omega) (by omega) (by omega)
    simpa [n, m, hn, h0, h1, h2, hσdA, hσgA, hσ0, hσ1] using hbase4
  · rw [cyclicWindow_four_eq]
    have h0 := hwrap 5 1 (by omega) (by omega) (by omega)
    have h1 := hwrap 5 2 (by omega) (by omega) (by omega)
    have h2 := hwrap 5 3 (by omega) (by omega) (by omega)
    simpa [n, m, hn, h0, h1, h2, hσgA, hσ0, hσ1, hσ2] using hbase5

end

end Rank4DangerousBranches
end HigherRankKUM
