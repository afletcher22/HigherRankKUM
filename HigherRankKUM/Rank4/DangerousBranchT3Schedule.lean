import HigherRankKUM.Rank4.DangerousBranchT3Geometry
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

/-- Every window beginning before the six-element tail of the t=3 pattern
is ordinary, provided the prefix follows the repeating A,B,C,G class pattern.

The hypothesis is deliberately stated as a residue-class invariant.  It
covers all complete ABCG blocks and the first three tail entries pA,pB,pC,
which continue residues 0,1,2 after the final G. -/
theorem dangerous_triple_ordinary_prefix_windows
    {M : Matroid α} {k : ℕ} {H₀ H₁ H₂ : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hH₂ : DangerousHyperplane M k H₂)
    (h01 : H₀ ≠ H₁) (h02 : H₀ ≠ H₂) (h12 : H₁ ≠ H₂)
    (σ : Fin (4 * k + 2) ≃ M.E)
    (hA : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 0 →
      (σ t : α) ∈ M.E \ H₀)
    (hB : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 1 →
      (σ t : α) ∈ M.E \ H₁)
    (hC : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 2 →
      (σ t : α) ∈ M.E \ H₂)
    (hG : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 3 →
      (σ t : α) ∈ (H₀ ∩ H₁) ∩ H₂) :
    let hn : 0 < 4 * k + 2 := by omega
    ∀ i : Fin (4 * k + 2), i.val < 4 * (k - 1) →
      M.IsBase (cyclicWindow 4 hn σ i) := by
  let hn : 0 < 4 * k + 2 := by omega
  intro i hi
  have hi3 : i.val + 3 < 4 * k + 2 := by omega
  let i1 : Fin (4 * k + 2) := ⟨i.val + 1, by omega⟩
  let i2 : Fin (4 * k + 2) := ⟨i.val + 2, by omega⟩
  let i3 : Fin (4 * k + 2) := ⟨i.val + 3, by omega⟩
  have hcy1 :
      cyclicIndex (4 * k + 2) hn i 1 = i1 := by
    simpa [i1] using
      cyclicIndex_eq_mk_add_of_lt (4 * k + 2) hn i 1 (by omega)
  have hcy2 :
      cyclicIndex (4 * k + 2) hn i 2 = i2 := by
    simpa [i2] using
      cyclicIndex_eq_mk_add_of_lt (4 * k + 2) hn i 2 (by omega)
  have hcy3 :
      cyclicIndex (4 * k + 2) hn i 3 = i3 := by
    simpa [i3] using
      cyclicIndex_eq_mk_add_of_lt (4 * k + 2) hn i 3 hi3
  rw [cyclicWindow_four_eq, hcy1, hcy2, hcy3]

  have hrem : i.val % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases hr : i.val % 4
  · have ha : (σ i : α) ∈ M.E \ H₀ :=
      hA i (by omega) hr
    have hb : (σ i1 : α) ∈ M.E \ H₁ :=
      hB i1 (by simp [i1]; omega) (by simp [i1]; omega)
    have hc : (σ i2 : α) ∈ M.E \ H₂ :=
      hC i2 (by simp [i2]; omega) (by simp [i2]; omega)
    have hg : (σ i3 : α) ∈ (H₀ ∩ H₁) ∩ H₂ :=
      hG i3 (by simp [i3]; omega) (by simp [i3]; omega)
    have hbase := dangerous_triple_one_each_isBase
      hk hE hRank hEcard hStrict hH₀ hH₁ hH₂ h01 h02 h12
      hg ha hb hc
    convert hbase using 1 <;> ext x <;>
      simp [Set.mem_insert_iff, or_comm, or_left_comm, or_assoc]
  · have hb : (σ i : α) ∈ M.E \ H₁ :=
      hB i (by omega) hr
    have hc : (σ i1 : α) ∈ M.E \ H₂ :=
      hC i1 (by simp [i1]; omega) (by simp [i1]; omega)
    have hg : (σ i2 : α) ∈ (H₀ ∩ H₁) ∩ H₂ :=
      hG i2 (by simp [i2]; omega) (by simp [i2]; omega)
    have ha : (σ i3 : α) ∈ M.E \ H₀ :=
      hA i3 (by simp [i3]; omega) (by simp [i3]; omega)
    have hbase := dangerous_triple_one_each_isBase
      hk hE hRank hEcard hStrict hH₀ hH₁ hH₂ h01 h02 h12
      hg ha hb hc
    convert hbase using 1 <;> ext x <;>
      simp [Set.mem_insert_iff, or_comm, or_left_comm, or_assoc]
  · have hc : (σ i : α) ∈ M.E \ H₂ :=
      hC i (by omega) hr
    have hg : (σ i1 : α) ∈ (H₀ ∩ H₁) ∩ H₂ :=
      hG i1 (by simp [i1]; omega) (by simp [i1]; omega)
    have ha : (σ i2 : α) ∈ M.E \ H₀ :=
      hA i2 (by simp [i2]; omega) (by simp [i2]; omega)
    have hb : (σ i3 : α) ∈ M.E \ H₁ :=
      hB i3 (by simp [i3]; omega) (by simp [i3]; omega)
    have hbase := dangerous_triple_one_each_isBase
      hk hE hRank hEcard hStrict hH₀ hH₁ hH₂ h01 h02 h12
      hg ha hb hc
    convert hbase using 1 <;> ext x <;>
      simp [Set.mem_insert_iff, or_comm, or_left_comm, or_assoc]
  · have hg : (σ i : α) ∈ (H₀ ∩ H₁) ∩ H₂ :=
      hG i (by omega) hr
    have ha : (σ i1 : α) ∈ M.E \ H₀ :=
      hA i1 (by simp [i1]; omega) (by simp [i1]; omega)
    have hb : (σ i2 : α) ∈ M.E \ H₁ :=
      hB i2 (by simp [i2]; omega) (by simp [i2]; omega)
    have hc : (σ i3 : α) ∈ M.E \ H₂ :=
      hC i3 (by simp [i3]; omega) (by simp [i3]; omega)
    have hbase := dangerous_triple_one_each_isBase
      hk hE hRank hEcard hStrict hH₀ hH₁ hH₂ h01 h02 h12
      hg ha hb hc
    convert hbase using 1 <;> ext x <;>
      simp [Set.mem_insert_iff, or_comm, or_left_comm, or_assoc]

/-- The six exceptional windows of the explicit t=3 schedule are bases.

The schedule is normalized so the first ordinary ABC entries are
qA,qB,qC, while the final six entries are
pA,pB,pC,dA,dB,dC. Thus the duplicated pairs are exactly
{pX,dX} inside the tail and {dX,qX} across the wrap. -/
theorem dangerous_triple_six_exceptional_windows
    {M : Matroid α} {k : ℕ} {H₀ H₁ H₂ : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hH₂ : DangerousHyperplane M k H₂)
    (h01 : H₀ ≠ H₁) (h02 : H₀ ≠ H₂) (h12 : H₁ ≠ H₂)
    (σ : Fin (4 * k + 2) ≃ M.E)
    {qA pA dA qB pB dB qC pC dC : α}
    (hqA : qA ∈ M.E \ H₀) (hpA : pA ∈ M.E \ H₀) (hdA : dA ∈ M.E \ H₀)
    (hqB : qB ∈ M.E \ H₁) (hpB : pB ∈ M.E \ H₁) (hdB : dB ∈ M.E \ H₁)
    (hqC : qC ∈ M.E \ H₂) (hpC : pC ∈ M.E \ H₂) (hdC : dC ∈ M.E \ H₂)
    (hpAdA : pA ≠ dA) (hdAqA : dA ≠ qA)
    (hpBdB : pB ≠ dB) (hdBqB : dB ≠ qB)
    (hpCdC : pC ≠ dC) (hdCqC : dC ≠ qC)
    (hpdA : M.Indep ({pA, dA} : Set α))
    (hdqA : M.Indep ({dA, qA} : Set α))
    (hpdB : M.Indep ({pB, dB} : Set α))
    (hdqB : M.Indep ({dB, qB} : Set α))
    (hpdC : M.Indep ({pC, dC} : Set α))
    (hdqC : M.Indep ({dC, qC} : Set α))
    (hσ0 : (σ ⟨0, by omega⟩ : α) = qA)
    (hσ1 : (σ ⟨1, by omega⟩ : α) = qB)
    (hσ2 : (σ ⟨2, by omega⟩ : α) = qC)
    (hσpA : (σ ⟨4 * (k - 1), by omega⟩ : α) = pA)
    (hσpB : (σ ⟨4 * (k - 1) + 1, by omega⟩ : α) = pB)
    (hσpC : (σ ⟨4 * (k - 1) + 2, by omega⟩ : α) = pC)
    (hσdA : (σ ⟨4 * (k - 1) + 3, by omega⟩ : α) = dA)
    (hσdB : (σ ⟨4 * (k - 1) + 4, by omega⟩ : α) = dB)
    (hσdC : (σ ⟨4 * (k - 1) + 5, by omega⟩ : α) = dC) :
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

  have hbaseA_pd : M.IsBase ({pA, pB, pC, dA} : Set α) := by
    have h := dangerous_triple_side_pair_isBase
      (M := M) (k := k) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂)
      (x := pA) (y := dA) (b := pB) (c := pC)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict
      hH₀ hH₁ hH₂ h01 h02 h12 hpA hdA hpAdA hpdA hpB hpC
    simpa [Set.pair_comm] using h

  have hbaseB_pd : M.IsBase ({pB, pC, dA, dB} : Set α) := by
    have h := dangerous_triple_side_pair_isBase
      (M := M) (k := k) (H₀ := H₁) (H₁ := H₂) (H₂ := H₀)
      (x := pB) (y := dB) (b := pC) (c := dA)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict
      hH₁ hH₂ hH₀ h12 h01.symm h02.symm
      hpB hdB hpBdB hpdB hpC hdA
    simpa [Set.pair_comm] using h

  have hbaseC_pd : M.IsBase ({pC, dA, dB, dC} : Set α) := by
    have h := dangerous_triple_side_pair_isBase
      (M := M) (k := k) (H₀ := H₂) (H₁ := H₀) (H₂ := H₁)
      (x := pC) (y := dC) (b := dA) (c := dB)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict
      hH₂ hH₀ hH₁ h02.symm h12.symm h01
      hpC hdC hpCdC hpdC hdA hdB
    simpa [Set.pair_comm] using h

  have hbaseA_dq : M.IsBase ({dA, dB, dC, qA} : Set α) := by
    have h := dangerous_triple_side_pair_isBase
      (M := M) (k := k) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂)
      (x := dA) (y := qA) (b := dB) (c := dC)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict
      hH₀ hH₁ hH₂ h01 h02 h12 hdA hqA hdAqA hdqA hdB hdC
    simpa [Set.pair_comm] using h

  have hbaseB_dq : M.IsBase ({dB, dC, qA, qB} : Set α) := by
    have h := dangerous_triple_side_pair_isBase
      (M := M) (k := k) (H₀ := H₁) (H₁ := H₂) (H₂ := H₀)
      (x := dB) (y := qB) (b := dC) (c := qA)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict
      hH₁ hH₂ hH₀ h12 h01.symm h02.symm
      hdB hqB hdBqB hdqB hdC hqA
    simpa [Set.pair_comm] using h

  have hbaseC_dq : M.IsBase ({dC, qA, qB, qC} : Set α) := by
    have h := dangerous_triple_side_pair_isBase
      (M := M) (k := k) (H₀ := H₂) (H₁ := H₀) (H₂ := H₁)
      (x := dC) (y := qC) (b := qA) (c := qB)
      (by omega : 1 ≤ k) hE hRank hEcard hStrict
      hH₂ hH₀ hH₁ h02.symm h12.symm h01
      hdC hqC hdCqC hdqC hqA hqB
    simpa [Set.pair_comm] using h

  dsimp only
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 0 1 (by omega)
    have h1 := hidx 0 2 (by omega)
    have h2 := hidx 0 3 (by omega)
    simpa [n, m, hn, h0, h1, h2, hσpA, hσpB, hσpC, hσdA] using hbaseA_pd
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 1 1 (by omega)
    have h1 := hidx 1 2 (by omega)
    have h2 := hidx 1 3 (by omega)
    simpa [n, m, hn, h0, h1, h2, hσpB, hσpC, hσdA, hσdB] using hbaseB_pd
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 2 1 (by omega)
    have h1 := hidx 2 2 (by omega)
    have h2 := hidx 2 3 (by omega)
    simpa [n, m, hn, h0, h1, h2, hσpC, hσdA, hσdB, hσdC] using hbaseC_pd
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 3 1 (by omega)
    have h1 := hidx 3 2 (by omega)
    have h2 := hwrap 3 3 (by omega) (by omega) (by omega)
    simpa [n, m, hn, h0, h1, h2, hσdA, hσdB, hσdC, hσ0] using hbaseA_dq
  constructor
  · rw [cyclicWindow_four_eq]
    have h0 := hidx 4 1 (by omega)
    have h1 := hwrap 4 2 (by omega) (by omega) (by omega)
    have h2 := hwrap 4 3 (by omega) (by omega) (by omega)
    simpa [n, m, hn, h0, h1, h2, hσdB, hσdC, hσ0, hσ1] using hbaseB_dq
  · rw [cyclicWindow_four_eq]
    have h0 := hwrap 5 1 (by omega) (by omega) (by omega)
    have h1 := hwrap 5 2 (by omega) (by omega) (by omega)
    have h2 := hwrap 5 3 (by omega) (by omega) (by omega)
    simpa [n, m, hn, h0, h1, h2, hσdC, hσ0, hσ1, hσ2] using hbaseC_dq


/-- A normalized t=3 schedule is a cyclic basis ordering.

The prefix follows A,B,C,G by residue mod four through the first pA,pB,pC
tail entries; the last six entries are pA,pB,pC,dA,dB,dC and the first three
entries are qA,qB,qC.  The two selected pairs through dX certify all six
exceptional windows. -/
theorem dangerous_triple_cbo_of_normalized_schedule
    {M : Matroid α} {k : ℕ} {H₀ H₁ H₂ : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hH₂ : DangerousHyperplane M k H₂)
    (h01 : H₀ ≠ H₁) (h02 : H₀ ≠ H₂) (h12 : H₁ ≠ H₂)
    (σ : Fin (4 * k + 2) ≃ M.E)
    (hA : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 0 →
      (σ t : α) ∈ M.E \ H₀)
    (hB : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 1 →
      (σ t : α) ∈ M.E \ H₁)
    (hC : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 2 →
      (σ t : α) ∈ M.E \ H₂)
    (hG : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 3 →
      (σ t : α) ∈ (H₀ ∩ H₁) ∩ H₂)
    {qA pA dA qB pB dB qC pC dC : α}
    (hqA : qA ∈ M.E \ H₀) (hpA : pA ∈ M.E \ H₀) (hdA : dA ∈ M.E \ H₀)
    (hqB : qB ∈ M.E \ H₁) (hpB : pB ∈ M.E \ H₁) (hdB : dB ∈ M.E \ H₁)
    (hqC : qC ∈ M.E \ H₂) (hpC : pC ∈ M.E \ H₂) (hdC : dC ∈ M.E \ H₂)
    (hpAdA : pA ≠ dA) (hdAqA : dA ≠ qA)
    (hpBdB : pB ≠ dB) (hdBqB : dB ≠ qB)
    (hpCdC : pC ≠ dC) (hdCqC : dC ≠ qC)
    (hpdA : M.Indep ({pA, dA} : Set α))
    (hdqA : M.Indep ({dA, qA} : Set α))
    (hpdB : M.Indep ({pB, dB} : Set α))
    (hdqB : M.Indep ({dB, qB} : Set α))
    (hpdC : M.Indep ({pC, dC} : Set α))
    (hdqC : M.Indep ({dC, qC} : Set α))
    (hσ0 : (σ ⟨0, by omega⟩ : α) = qA)
    (hσ1 : (σ ⟨1, by omega⟩ : α) = qB)
    (hσ2 : (σ ⟨2, by omega⟩ : α) = qC)
    (hσpA : (σ ⟨4 * (k - 1), by omega⟩ : α) = pA)
    (hσpB : (σ ⟨4 * (k - 1) + 1, by omega⟩ : α) = pB)
    (hσpC : (σ ⟨4 * (k - 1) + 2, by omega⟩ : α) = pC)
    (hσdA : (σ ⟨4 * (k - 1) + 3, by omega⟩ : α) = dA)
    (hσdB : (σ ⟨4 * (k - 1) + 4, by omega⟩ : α) = dB)
    (hσdC : (σ ⟨4 * (k - 1) + 5, by omega⟩ : α) = dC) :
    CyclicBasisOrder M 4 (by omega) σ := by
  let hn : 0 < 4 * k + 2 := by omega
  have hOrd :=
    dangerous_triple_ordinary_prefix_windows
      hk hE hRank hEcard hStrict hH₀ hH₁ hH₂ h01 h02 h12
      σ hA hB hC hG
  have hExc :=
    dangerous_triple_six_exceptional_windows
      hk hE hRank hEcard hStrict hH₀ hH₁ hH₂ h01 h02 h12
      σ hqA hpA hdA hqB hpB hdB hqC hpC hdC
      hpAdA hdAqA hpBdB hdBqB hpCdC hdCqC
      hpdA hdqA hpdB hdqB hpdC hdqC
      hσ0 hσ1 hσ2 hσpA hσpB hσpC hσdA hσdB hσdC
  intro i
  by_cases hi : i.val < 4 * (k - 1)
  · simpa [hn] using hOrd i hi
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
  · simpa [hiEq 0 rfl, hn] using h0
  · simpa [hiEq 1 rfl, hn] using h1
  · simpa [hiEq 2 rfl, hn] using h2
  · simpa [hiEq 3 rfl, hn] using h3
  · simpa [hiEq 4 rfl, hn] using h4
  · simpa [hiEq 5 rfl, hn] using h5


/-- Local enumerations of the four t=3 parts, with the three distinguished
side slots normalized, interleave to a cyclic basis ordering. -/
theorem dangerous_triple_cbo_of_local_orders
    {M : Matroid α} {k : ℕ} {H₀ H₁ H₂ : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH₀ : DangerousHyperplane M k H₀)
    (hH₁ : DangerousHyperplane M k H₁)
    (hH₂ : DangerousHyperplane M k H₂)
    (h01 : H₀ ≠ H₁) (h02 : H₀ ≠ H₂) (h12 : H₁ ≠ H₂)
    (eA : Fin (k + 1) ≃ (M.E \ H₀))
    (eB : Fin (k + 1) ≃ (M.E \ H₁))
    (eC : Fin (k + 1) ≃ (M.E \ H₂))
    (eG : Fin (k - 1) ≃ ((H₀ ∩ H₁) ∩ H₂))
    {qA pA dA qB pB dB qC pC dC : α}
    (heA0 : (eA ⟨0, by omega⟩ : α) = qA)
    (heAp : (eA ⟨k - 1, by omega⟩ : α) = pA)
    (heAd : (eA ⟨k, by omega⟩ : α) = dA)
    (heB0 : (eB ⟨0, by omega⟩ : α) = qB)
    (heBp : (eB ⟨k - 1, by omega⟩ : α) = pB)
    (heBd : (eB ⟨k, by omega⟩ : α) = dB)
    (heC0 : (eC ⟨0, by omega⟩ : α) = qC)
    (heCp : (eC ⟨k - 1, by omega⟩ : α) = pC)
    (heCd : (eC ⟨k, by omega⟩ : α) = dC)
    (hpAdA : pA ≠ dA) (hdAqA : dA ≠ qA)
    (hpBdB : pB ≠ dB) (hdBqB : dB ≠ qB)
    (hpCdC : pC ≠ dC) (hdCqC : dC ≠ qC)
    (hpdA : M.Indep ({pA, dA} : Set α))
    (hdqA : M.Indep ({dA, qA} : Set α))
    (hpdB : M.Indep ({pB, dB} : Set α))
    (hdqB : M.Indep ({dB, qB} : Set α))
    (hpdC : M.Indep ({pC, dC} : Set α))
    (hdqC : M.Indep ({dC, qC} : Set α)) :
    ∃ σ : Fin (4 * k + 2) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) σ := by
  let eSlots :
      FiniteSchedule.T3Slots k ≃
        ((M.E \ H₀) ⊕ (M.E \ H₁)) ⊕
          ((M.E \ H₂) ⊕ ((H₀ ∩ H₁) ∩ H₂)) :=
    Equiv.sumCongr (Equiv.sumCongr eA eB) (Equiv.sumCongr eC eG)
  let eGround :=
    dangerous_triple_parts_equiv_ground
      hE hRank hEcard hStrict hH₀ hH₁ hH₂ h01 h02 h12
  let σ : Fin (4 * k + 2) ≃ M.E :=
    (FiniteSchedule.t3IndexEquiv k hk).trans (eSlots.trans eGround)

  have hslotA (a : Fin (k + 1)) :
      (eGround (Sum.inl (Sum.inl (eA a))) : α) = (eA a : α) := by
    simp [eGround, dangerous_triple_parts_equiv_ground]
  have hslotB (b : Fin (k + 1)) :
      (eGround (Sum.inl (Sum.inr (eB b))) : α) = (eB b : α) := by
    simp [eGround, dangerous_triple_parts_equiv_ground]
  have hslotC (cc : Fin (k + 1)) :
      (eGround (Sum.inr (Sum.inl (eC cc))) : α) = (eC cc : α) := by
    simp [eGround, dangerous_triple_parts_equiv_ground]
  have hslotG (g : Fin (k - 1)) :
      (eGround (Sum.inr (Sum.inr (eG g))) : α) = (eG g : α) := by
    simp [eGround, dangerous_triple_parts_equiv_ground]

  have hprefix_eval (j : Fin (k - 1)) (r : Fin 4) :
      (σ ⟨r.val + 4 * j.val, by omega⟩ : α) =
        match r.val with
        | 0 => (eA ⟨j.val, by omega⟩ : α)
        | 1 => (eB ⟨j.val, by omega⟩ : α)
        | 2 => (eC ⟨j.val, by omega⟩ : α)
        | _ => (eG j : α) := by
    fin_cases r <;>
      simp [σ, eSlots, FiniteSchedule.t3IndexEquiv_prefix,
        FiniteSchedule.t3PrefixSlot, hslotA, hslotB, hslotC, hslotG]

  have htail_eval (r : Fin 6) :
      (σ ⟨4 * (k - 1) + r.val, by omega⟩ : α) =
        match r.val with
        | 0 => (eA ⟨k - 1, by omega⟩ : α)
        | 1 => (eB ⟨k - 1, by omega⟩ : α)
        | 2 => (eC ⟨k - 1, by omega⟩ : α)
        | 3 => (eA ⟨k, by omega⟩ : α)
        | 4 => (eB ⟨k, by omega⟩ : α)
        | _ => (eC ⟨k, by omega⟩ : α) := by
    fin_cases r <;>
      simp [σ, eSlots, FiniteSchedule.t3IndexEquiv_tail,
        FiniteSchedule.t3TailSlot, hslotA, hslotB, hslotC]

  have hA : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 0 →
      (σ t : α) ∈ M.E \ H₀ := by
    intro t ht hmod
    by_cases hpref : t.val < 4 * (k - 1)
    · let j : Fin (k - 1) := ⟨t.val / 4, by omega⟩
      have hdecomp : t.val = 0 + 4 * j.val := by
        dsimp [j]
        have hm := Nat.mod_add_div t.val 4
        omega
      have htEq : t = ⟨0 + 4 * j.val, by omega⟩ := by
        apply Fin.ext
        simpa [hdecomp]
      rw [htEq, hprefix_eval j 0]
      exact (eA ⟨j.val, by omega⟩).property
    · have htval : t.val = 4 * (k - 1) := by
        have h4 : (4 * (k - 1)) % 4 = 0 := by simp
        omega
      have htEq : t = ⟨4 * (k - 1), by omega⟩ := by
        apply Fin.ext
        exact htval
      rw [htEq]
      simpa using (eA ⟨k - 1, by omega⟩).property

  have hB : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 1 →
      (σ t : α) ∈ M.E \ H₁ := by
    intro t ht hmod
    by_cases hpref : t.val < 4 * (k - 1)
    · let j : Fin (k - 1) := ⟨t.val / 4, by omega⟩
      have hdecomp : t.val = 1 + 4 * j.val := by
        dsimp [j]
        have hm := Nat.mod_add_div t.val 4
        omega
      have htEq : t = ⟨1 + 4 * j.val, by omega⟩ := by
        apply Fin.ext
        simpa [hdecomp]
      rw [htEq, hprefix_eval j 1]
      exact (eB ⟨j.val, by omega⟩).property
    · have htval : t.val = 4 * (k - 1) + 1 := by omega
      have htEq : t = ⟨4 * (k - 1) + 1, by omega⟩ := by
        apply Fin.ext
        exact htval
      rw [htEq]
      simpa using (eB ⟨k - 1, by omega⟩).property

  have hC : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 2 →
      (σ t : α) ∈ M.E \ H₂ := by
    intro t ht hmod
    by_cases hpref : t.val < 4 * (k - 1)
    · let j : Fin (k - 1) := ⟨t.val / 4, by omega⟩
      have hdecomp : t.val = 2 + 4 * j.val := by
        dsimp [j]
        have hm := Nat.mod_add_div t.val 4
        omega
      have htEq : t = ⟨2 + 4 * j.val, by omega⟩ := by
        apply Fin.ext
        simpa [hdecomp]
      rw [htEq, hprefix_eval j 2]
      exact (eC ⟨j.val, by omega⟩).property
    · have htval : t.val = 4 * (k - 1) + 2 := by omega
      have htEq : t = ⟨4 * (k - 1) + 2, by omega⟩ := by
        apply Fin.ext
        exact htval
      rw [htEq]
      simpa using (eC ⟨k - 1, by omega⟩).property

  have hG : ∀ t : Fin (4 * k + 2),
      t.val < 4 * (k - 1) + 3 → t.val % 4 = 3 →
      (σ t : α) ∈ (H₀ ∩ H₁) ∩ H₂ := by
    intro t ht hmod
    have hpref : t.val < 4 * (k - 1) := by omega
    let j : Fin (k - 1) := ⟨t.val / 4, by omega⟩
    have hdecomp : t.val = 3 + 4 * j.val := by
      dsimp [j]
      have hm := Nat.mod_add_div t.val 4
      omega
    have htEq : t = ⟨3 + 4 * j.val, by omega⟩ := by
      apply Fin.ext
      simpa [hdecomp]
    rw [htEq, hprefix_eval j 3]
    exact (eG j).property

  have hσ0 : (σ ⟨0, by omega⟩ : α) = qA := by
    have h := hprefix_eval ⟨0, by omega⟩ 0
    simpa [heA0] using h
  have hσ1 : (σ ⟨1, by omega⟩ : α) = qB := by
    have h := hprefix_eval ⟨0, by omega⟩ 1
    simpa [heB0] using h
  have hσ2 : (σ ⟨2, by omega⟩ : α) = qC := by
    have h := hprefix_eval ⟨0, by omega⟩ 2
    simpa [heC0] using h

  have hσpA : (σ ⟨4 * (k - 1), by omega⟩ : α) = pA := by
    have h := htail_eval 0
    simpa [heAp] using h
  have hσpB : (σ ⟨4 * (k - 1) + 1, by omega⟩ : α) = pB := by
    have h := htail_eval 1
    simpa [heBp] using h
  have hσpC : (σ ⟨4 * (k - 1) + 2, by omega⟩ : α) = pC := by
    have h := htail_eval 2
    simpa [heCp] using h
  have hσdA : (σ ⟨4 * (k - 1) + 3, by omega⟩ : α) = dA := by
    have h := htail_eval 3
    simpa [heAd] using h
  have hσdB : (σ ⟨4 * (k - 1) + 4, by omega⟩ : α) = dB := by
    have h := htail_eval 4
    simpa [heBd] using h
  have hσdC : (σ ⟨4 * (k - 1) + 5, by omega⟩ : α) = dC := by
    have h := htail_eval 5
    simpa [heCd] using h

  refine ⟨σ, ?_⟩
  exact dangerous_triple_cbo_of_normalized_schedule
    hk hE hRank hEcard hStrict hH₀ hH₁ hH₂ h01 h02 h12
    σ hA hB hC hG
    (eA ⟨0, by omega⟩).property (eA ⟨k - 1, by omega⟩).property
    (eA ⟨k, by omega⟩).property
    (eB ⟨0, by omega⟩).property (eB ⟨k - 1, by omega⟩).property
    (eB ⟨k, by omega⟩).property
    (eC ⟨0, by omega⟩).property (eC ⟨k - 1, by omega⟩).property
    (eC ⟨k, by omega⟩).property
    hpAdA hdAqA hpBdB hdBqB hpCdC hdCqC
    hpdA hdqA hpdB hdqB hpdC hdqC
    hσ0 hσ1 hσ2 hσpA hσpB hσpC hσdA hσdB hσdC

end

end Rank4DangerousBranches
end HigherRankKUM
