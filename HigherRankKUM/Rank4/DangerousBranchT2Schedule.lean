import HigherRankKUM.Rank4.DangerousBranchFactors
import HigherRankKUM.Rank4.DangerousBranchT2Good
import HigherRankKUM.Rank4.CyclicPigeonhole
import HigherRankKUM.CyclicRotation
import HigherRankKUM.Rank4.CyclicWindowFour
import HigherRankKUM.Rank4.CyclicIndexArithmetic
import HigherRankKUM.Rank4.FiniteSchedule

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

  have hwrap (r s : ℕ) (hr : r < 6) (hge : 6 ≤ r + s)
      (hlt : r + s < 12) :
      cyclicIndex n hnpos ⟨m + r, by omega⟩ s =
        ⟨r + s - 6, by omega⟩ := by
    have h := cyclicIndex_eq_mk_sub_of_ge_of_lt_two_mul
      n hnpos ⟨m + r, by omega⟩ s (by omega) (by omega)
    rw [h]
    apply Fin.ext
    dsimp [m, n]
    omega

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
    rw [h0, h1, h2, hσpA, hσpB, hσgB, hσdB]
    exact hbase0
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 1 1 (by omega)
    have h1 := hidx 1 2 (by omega)
    have h2 := hidx 1 3 (by omega)
    rw [h0, h1, h2, hσpB, hσgB, hσdB, hσdA]
    exact hbase1
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 2 1 (by omega)
    have h1 := hidx 2 2 (by omega)
    have h2 := hidx 2 3 (by omega)
    rw [h0, h1, h2, hσgB, hσdB, hσdA, hσgA]
    exact hbase2
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 3 1 (by omega)
    have h1 := hidx 3 2 (by omega)
    have h2 := hwrap 3 3 (by omega) (by omega) (by omega)
    rw [h0, h1, h2, hσdB, hσdA, hσgA, hσ0]
    exact hbase3
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 4 1 (by omega)
    have h1 := hwrap 4 2 (by omega) (by omega) (by omega)
    have h2 := hwrap 4 3 (by omega) (by omega) (by omega)
    rw [h0, h1, h2, hσdA, hσgA, hσ0, hσ1]
    exact hbase4
  · rw [cyclicWindow_four_eq]
    have h0 := hwrap 5 1 (by omega) (by omega) (by omega)
    have h1 := hwrap 5 2 (by omega) (by omega) (by omega)
    have h2 := hwrap 5 3 (by omega) (by omega) (by omega)
    rw [h0, h1, h2, hσgA, hσ0, hσ1, hσ2]
    exact hbase5


/-- Two distinct dangerous hyperplanes directly yield a rank-four cyclic
basis ordering for k >= 2. The six-element case k=1 is handled separately by
the rank-four six-element boundary theorem. -/
theorem exists_cyclicBasisOrder_of_two_dangerous
    {M : Matroid α} {k : ℕ}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    {H K : Set α}
    (hH : DangerousHyperplane M k H)
    (hK : DangerousHyperplane M k K)
    (hne : H ≠ K) :
    ∃ σ : Fin (4 * k + 2) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) σ := by
  obtain ⟨order, hOrder⟩ :=
    exists_core_cbo_of_two_dangerous
      (M := M) (k := k) (H := H) (K := K)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict hH hK hne

  obtain ⟨j, b₀, b₁, a₀, a₁,
      hb₀, hb₁, hbne, ha₀, ha₁, hane, hbBasis, haBasis⟩ :=
    dangerous_two_exists_oriented_good_core_edge
      (M := M) (k := k) (H := H) (K := K)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict hH hK hne order hOrder

  obtain ⟨order', hOrder', hlastB, hlastA⟩ :=
    exists_shifted_core_cbo_with_edge_at_end
      (M := M) (k := k) (H := H) (K := K)
      (by omega : 1 ≤ k) order hOrder j

  have hAfin : (M.E \ H).Finite := hE.sdiff
  have hBfin : (M.E \ K).Finite := hE.sdiff
  have hAcard : (M.E \ H).ncard = k + 1 :=
    dangerous_complement_ncard_eq hE hEcard hH
  have hBcard : (M.E \ K).ncard = k + 1 :=
    dangerous_complement_ncard_eq hE hEcard hK

  let iAk : Fin (k + 1) := ⟨k, by omega⟩
  let iA0 : Fin (k + 1) := ⟨0, by omega⟩
  have hiA : iAk ≠ iA0 := by
    intro h
    have := congrArg Fin.val h
    simp [iAk, iA0] at this
    omega
  obtain ⟨eA, heAk, heA0⟩ :=
    FiniteSchedule.exists_fin_equiv_with_two_prescribed
      hAfin hAcard iAk iA0 hiA ha₀ ha₁ hane

  let iBp : Fin (k + 1) := ⟨k - 1, by omega⟩
  let iBd : Fin (k + 1) := ⟨k, by omega⟩
  have hiB : iBp ≠ iBd := by
    intro h
    have := congrArg Fin.val h
    simp [iBp, iBd] at this
    omega
  obtain ⟨eB, heBp, heBd⟩ :=
    FiniteSchedule.exists_fin_equiv_with_two_prescribed
      hBfin hBcard iBp iBd hiB hb₀ hb₁ hbne

  let eG : Fin (2 * k) ≃ (H ∩ K : Set α) :=
    order'.trans (Equiv.setCongr (by simp))

  let eSlots :
      FiniteSchedule.T2Slots k ≃
        ((M.E \ H) ⊕ (M.E \ K)) ⊕ (H ∩ K) :=
    Equiv.sumCongr (Equiv.sumCongr eA eB) eG
  let eGround :=
    dangerous_two_parts_equiv_ground
      hE hRank hEcard hStrict hH hK hne
  let σ : Fin (4 * k + 2) ≃ M.E :=
    (FiniteSchedule.t2IndexEquiv k hk).trans (eSlots.trans eGround)

  have hslotA (a : Fin (k + 1)) :
      (eGround (Sum.inl (Sum.inl (eA a))) : α) = (eA a : α) := by
    simp [eGround, dangerous_two_parts_equiv_ground]
  have hslotB (b : Fin (k + 1)) :
      (eGround (Sum.inl (Sum.inr (eB b))) : α) = (eB b : α) := by
    simp [eGround, dangerous_two_parts_equiv_ground]
  have hslotG (g : Fin (2 * k)) :
      (eGround (Sum.inr (eG g)) : α) = (eG g : α) := by
    simp [eGround, dangerous_two_parts_equiv_ground]

  have hprefix_eval (q : Fin (k - 1)) (r : Fin 4) :
      (σ ⟨r.val + 4 * q.val, by omega⟩ : α) =
        match r.val with
        | 0 => (eA ⟨q.val, by omega⟩ : α)
        | 1 => (eB ⟨q.val, by omega⟩ : α)
        | 2 => (order' ⟨2 * q.val, by omega⟩ : α)
        | _ => (order' ⟨2 * q.val + 1, by omega⟩ : α) := by
    fin_cases r <;>
      simp [σ, eSlots, eG, FiniteSchedule.t2IndexEquiv_prefix,
        FiniteSchedule.t2PrefixSlot, hslotA, hslotB, hslotG]

  have htail_eval (r : Fin 6) :
      (σ ⟨4 * (k - 1) + r.val, by omega⟩ : α) =
        match r.val with
        | 0 => (eA ⟨k - 1, by omega⟩ : α)
        | 1 => (eB ⟨k - 1, by omega⟩ : α)
        | 2 => (order' ⟨2 * k - 2, by omega⟩ : α)
        | 3 => (eB ⟨k, by omega⟩ : α)
        | 4 => (eA ⟨k, by omega⟩ : α)
        | _ => (order' ⟨2 * k - 1, by omega⟩ : α) := by
    fin_cases r <;>
      simp [σ, eSlots, eG, FiniteSchedule.t2IndexEquiv_tail,
        FiniteSchedule.t2TailSlot, hslotA, hslotB, hslotG]

  have hApos : ∀ q : Fin k,
      (σ ⟨4 * q.val, by omega⟩ : α) ∈ M.E \ H := by
    intro q
    by_cases hq : q.val < k - 1
    · let j' : Fin (k - 1) := ⟨q.val, hq⟩
      have h := hprefix_eval j' 0
      rw [show (⟨4 * q.val, by omega⟩ : Fin (4 * k + 2)) =
          ⟨0 + 4 * j'.val, by omega⟩ by apply Fin.ext; simp [j']]
      rw [h]
      exact (eA ⟨j'.val, by omega⟩).property
    · have hqeq : q.val = k - 1 := by omega
      have h := htail_eval 0
      rw [show (⟨4 * q.val, by omega⟩ : Fin (4 * k + 2)) =
          ⟨4 * (k - 1), by omega⟩ by apply Fin.ext; omega]
      rw [h]
      exact (eA ⟨k - 1, by omega⟩).property

  have hBpos : ∀ q : Fin k,
      (σ ⟨4 * q.val + 1, by omega⟩ : α) ∈ M.E \ K := by
    intro q
    by_cases hq : q.val < k - 1
    · let j' : Fin (k - 1) := ⟨q.val, hq⟩
      have h := hprefix_eval j' 1
      rw [show (⟨4 * q.val + 1, by omega⟩ : Fin (4 * k + 2)) =
          ⟨1 + 4 * j'.val, by omega⟩ by apply Fin.ext; simp [j']; omega]
      rw [h]
      exact (eB ⟨j'.val, by omega⟩).property
    · have hqeq : q.val = k - 1 := by omega
      have h := htail_eval 1
      rw [show (⟨4 * q.val + 1, by omega⟩ : Fin (4 * k + 2)) =
          ⟨4 * (k - 1) + 1, by omega⟩ by apply Fin.ext; omega]
      rw [h]
      exact (eB ⟨k - 1, by omega⟩).property

  have hG0pos : ∀ q : Fin k,
      (σ ⟨4 * q.val + 2, by omega⟩ : α) =
        (order' ⟨2 * q.val, by omega⟩ : α) := by
    intro q
    by_cases hq : q.val < k - 1
    · let j' : Fin (k - 1) := ⟨q.val, hq⟩
      have h := hprefix_eval j' 2
      rw [show (⟨4 * q.val + 2, by omega⟩ : Fin (4 * k + 2)) =
          ⟨2 + 4 * j'.val, by omega⟩ by apply Fin.ext; simp [j']; omega]
      simpa [j'] using h
    · have hqeq : q.val = k - 1 := by omega
      have h := htail_eval 2
      rw [show (⟨4 * q.val + 2, by omega⟩ : Fin (4 * k + 2)) =
          ⟨4 * (k - 1) + 2, by omega⟩ by apply Fin.ext; omega]
      simpa [hqeq] using h

  have hG1pos : ∀ q : Fin (k - 1),
      (σ ⟨4 * q.val + 3, by omega⟩ : α) =
        (order' ⟨2 * q.val + 1, by omega⟩ : α) := by
    intro q
    have h := hprefix_eval q 3
    simpa using h

  have hOrd :=
    dangerous_two_ordinary_prefix_windows
      hk hE hRank hEcard hStrict hH hK hne
      σ order' hOrder' hApos hBpos hG0pos hG1pos

  have hbBasis' :
      M.IsBasis
        ({(order' ⟨2 * k - 2, by omega⟩ : α), b₀, b₁} : Set α) H := by
    simpa [hlastB] using hbBasis
  have haBasis' :
      M.IsBasis
        ({(order' ⟨2 * k - 1, by omega⟩ : α), a₀, a₁} : Set α) K := by
    simpa [hlastA] using haBasis

  have hpairBA := dangerous_two_core_order_adjacent_indep
    (M := M) (k := k) (H := H) (K := K)
    (by omega : 1 ≤ k) order' hOrder'
    (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
  have hnextBA :
      cyclicIndex (2 * k) (by omega)
        (⟨2 * k - 2, by omega⟩ : Fin (2 * k)) 1 =
        ⟨2 * k - 1, by omega⟩ := by
    apply cyclicIndex_eq_mk_add_of_lt
    omega
  rw [hnextBA] at hpairBA

  have hpairA0 := dangerous_two_core_order_adjacent_indep
    (M := M) (k := k) (H := H) (K := K)
    (by omega : 1 ≤ k) order' hOrder'
    (⟨2 * k - 1, by omega⟩ : Fin (2 * k))
  have hnextA0 :
      cyclicIndex (2 * k) (by omega)
        (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) 1 =
        ⟨0, by omega⟩ := by
    apply Fin.ext
    simp [cyclicIndex]
    omega
  rw [hnextA0] at hpairA0

  have hgBneA :
      (order' ⟨2 * k - 2, by omega⟩ : α) ≠
        (order' ⟨2 * k - 1, by omega⟩ : α) := by
    intro h
    apply order'.injective
    apply Subtype.ext
    exact h
  have hgAne0 :
      (order' ⟨2 * k - 1, by omega⟩ : α) ≠
        (order' ⟨0, by omega⟩ : α) := by
    intro h
    apply order'.injective
    apply Subtype.ext
    exact h

  have hσ0 : (σ ⟨0, by omega⟩ : α) = a₁ := by
    have h := hprefix_eval ⟨0, by omega⟩ 0
    simpa [iA0, heA0] using h
  have hσ1 :
      (σ ⟨1, by omega⟩ : α) = (eB ⟨0, by omega⟩ : α) := by
    have h := hprefix_eval ⟨0, by omega⟩ 1
    simpa using h
  have hσ2 :
      (σ ⟨2, by omega⟩ : α) = (order' ⟨0, by omega⟩ : α) := by
    have h := hprefix_eval ⟨0, by omega⟩ 2
    simpa using h
  have hσpA :
      (σ ⟨4 * (k - 1), by omega⟩ : α) =
        (eA ⟨k - 1, by omega⟩ : α) := by
    have h := htail_eval 0
    simpa using h
  have hσpB :
      (σ ⟨4 * (k - 1) + 1, by omega⟩ : α) = b₀ := by
    have h := htail_eval 1
    simpa [iBp, heBp] using h
  have hσgB :
      (σ ⟨4 * (k - 1) + 2, by omega⟩ : α) =
        (order' ⟨2 * k - 2, by omega⟩ : α) := by
    have h := htail_eval 2
    simpa using h
  have hσdB :
      (σ ⟨4 * (k - 1) + 3, by omega⟩ : α) = b₁ := by
    have h := htail_eval 3
    simpa [iBd, heBd] using h
  have hσdA :
      (σ ⟨4 * (k - 1) + 4, by omega⟩ : α) = a₀ := by
    have h := htail_eval 4
    simpa [iAk, heAk] using h
  have hσgA :
      (σ ⟨4 * (k - 1) + 5, by omega⟩ : α) =
        (order' ⟨2 * k - 1, by omega⟩ : α) := by
    have h := htail_eval 5
    simpa using h

  have hExc :=
    dangerous_two_six_exceptional_windows
      hk hE hRank hEcard hStrict hH hK hne σ
      ha₁ (eA ⟨k - 1, by omega⟩).property ha₀
      (eB ⟨0, by omega⟩).property hb₀ hb₁
      (by simpa using (order' ⟨0, by omega⟩).property)
      (by simpa using (order' ⟨2 * k - 2, by omega⟩).property)
      (by simpa using (order' ⟨2 * k - 1, by omega⟩).property)
      hgBneA hgAne0 hpairBA hpairA0 hbBasis' haBasis'
      hσ0 hσ1 hσ2 hσpA hσpB hσgB hσdB hσdA hσgA

  refine ⟨σ, ?_⟩
  intro i
  by_cases hi : i.val < 4 * (k - 1)
  · simpa using hOrd i hi
  have hilow : 4 * (k - 1) ≤ i.val := Nat.le_of_not_gt hi
  have hiup : i.val < 4 * (k - 1) + 6 := by
    have := i.isLt
    omega
  let r := i.val - 4 * (k - 1)
  have hr : r < 6 := by
    dsimp [r]
    omega
  have hiEq (s : ℕ) (hs : r = s) :
      i = ⟨4 * (k - 1) + s, by omega⟩ := by
    apply Fin.ext
    dsimp [r] at hs
    omega
  rcases hExc with ⟨h0, h1, h2, h3, h4, h5⟩
  interval_cases r
  · simpa [hiEq 0 rfl] using h0
  · simpa [hiEq 1 rfl] using h1
  · simpa [hiEq 2 rfl] using h2
  · simpa [hiEq 3 rfl] using h3
  · simpa [hiEq 4 rfl] using h4
  · simpa [hiEq 5 rfl] using h5

end

end Rank4DangerousBranches
end HigherRankKUM
