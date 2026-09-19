import HigherRankKUM.Rank4.DangerousBranchT3Geometry
import HigherRankKUM.Rank4.CyclicWindowFour
import HigherRankKUM.Rank4.CyclicIndexArithmetic

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid
open Rank4GcdTwoDeletion

noncomputable section

variable {α : Type*}

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

end

end Rank4DangerousBranches
end HigherRankKUM
