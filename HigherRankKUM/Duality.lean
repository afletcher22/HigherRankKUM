import HigherRankKUM.FullSolver
import HigherRankKUM.CyclicOrder
import Mathlib.Combinatorics.Matroid.Dual
import Mathlib.Tactic

/-!
# Duality for KUM

Uniform density is self-dual: if `r · |X| ≤ n · r(X)` for every `X`, then
`(n - r) · |X| ≤ n · r*(X)` for every `X`. A cyclic basis ordering of the dual `M✶` by windows of
length `n - r` is a cyclic basis ordering of `M` by windows of length `r`
(`cyclicBasisOrder_of_dual`). So KUM at rank `r` and size `n` is equivalent to KUM at rank `n - r`
and size `n`.

* `UniformlyDenseRatio.dual`: uniform density passes to the dual.
* `SolvesKUMAtRankSize.of_dual`: KUM at `(n - r, n)` implies KUM at `(r, n)`.
* `solvesKUMAtRankSize_dual_iff`: the equivalence.
* `solvesKUMAtRankSize_self`: KUM at `(r, r)`, where the ground set is a basis.
-/

namespace HigherRankKUM

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- The dual of a rank-`r` matroid on `n` elements has rank `n - r`. -/
theorem eRank_dual_eq_sub
    (M : Matroid α) {n r : ℕ}
    (hRank : M.eRank = (r : ℕ∞))
    (hEcard : M.E.encard = (n : ℕ∞)) :
    M✶.eRank = ((n - r : ℕ) : ℕ∞) := by
  have h := M.eRank_add_eRank_dual
  rw [hRank, hEcard] at h
  have hle : M✶.eRank ≤ (n : ℕ∞) := by
    rw [← h]
    exact le_add_self
  obtain ⟨d, hd, _⟩ := ENat.le_natCast_iff.mp hle
  rw [hd] at h ⊢
  have hnat : r + d = n := by exact_mod_cast h
  have hdn : d = n - r := by omega
  rw [hdn]

/-- **Uniform density is self-dual.** If `M` has rank `r` on `n` elements and
`r · |X| ≤ n · r(X)` for every `X`, then `(n - r) · |X| ≤ n · r*(X)` for every `X`. -/
theorem UniformlyDenseRatio.dual
    (M : Matroid α) {n r : ℕ}
    (hE : M.E.Finite)
    (hRank : M.eRank = (r : ℕ∞))
    (hEcard : M.E.encard = (n : ℕ∞))
    (hDense : UniformlyDenseRatio M n r) :
    UniformlyDenseRatio M✶ n (n - r) := by
  have hrn : r ≤ n := by
    have h := M.eRk_le_encard M.E
    rw [M.eRk_ground, hRank, hEcard] at h
    exact_mod_cast h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrn
  rw [Nat.add_sub_cancel_left]
  intro X hX
  have hXE : X ⊆ M.E := by simpa using hX
  have hXfin : X.Finite := hE.subset hXE
  have hCfin : (M.E \ X).Finite := hE.sdiff
  have hCsub : M.E \ X ⊆ M.E := Set.sdiff_subset
  -- the rank of the complement in `M` and the dual rank of `X`, as natural numbers
  have hCrkBound : M.eRk (M.E \ X) ≤ (r : ℕ∞) := by
    rw [← hRank]
    exact M.eRk_le_eRank _
  obtain ⟨c, hCrk, _⟩ := ENat.le_natCast_iff.mp hCrkBound
  have hDrkBound : M✶.eRk X ≤ (X.ncard : ℕ∞) := by
    rw [hXfin.cast_ncard_eq]
    exact M✶.eRk_le_encard X
  obtain ⟨d, hDrk, _⟩ := ENat.le_natCast_iff.mp hDrkBound
  have hsplit : (M.E \ X).ncard + X.ncard = r + m := by
    have h := Set.encard_sdiff_add_encard_of_subset hXE
    rw [hEcard, ← hCfin.cast_ncard_eq, ← hXfin.cast_ncard_eq] at h
    exact_mod_cast h
  -- density of `M` on the complement of `X`
  have hd : r * (M.E \ X).ncard ≤ (r + m) * c := by
    have h := hDense (M.E \ X) hCsub
    rw [← hCfin.cast_ncard_eq, hCrk] at h
    exact_mod_cast h
  -- the dual rank formula `r*(X) + r(M) = r(E - X) + |X|`
  have hdual : d + r = c + X.ncard := by
    have h := M.eRk_dual_add_eRank X hXE
    rw [hDrk, hRank, hCrk, ← hXfin.cast_ncard_eq] at h
    exact_mod_cast h
  have e1 : (r + m) * (d + r) = (r + m) * (c + X.ncard) := by rw [hdual]
  have e2 : r * ((M.E \ X).ncard + X.ncard) = r * (r + m) := by rw [hsplit]
  have hgoal : m * X.ncard ≤ (r + m) * d := by nlinarith [hd, e1, e2]
  rw [← hXfin.cast_ncard_eq, hDrk]
  exact_mod_cast hgoal

/-- **KUM is self-dual.** KUM at rank `n - r` and size `n` implies KUM at rank `r` and size
`n`: order the dual, and read the same cyclic order with windows of the complementary length. -/
theorem SolvesKUMAtRankSize.of_dual {r n : ℕ} (hrn : r < n)
    (hSolve : SolvesKUMAtRankSize α (n - r) n) :
    SolvesKUMAtRankSize α r n := by
  intro N _hr hn hE hRank hEcard hDense
  have hDualRank : N✶.eRank = ((n - r : ℕ) : ℕ∞) := eRank_dual_eq_sub N hRank hEcard
  have hDualE : N✶.E.Finite := by simpa using hE
  have hDualCard : N✶.E.encard = (n : ℕ∞) := by simpa using hEcard
  have hDualDense : UniformlyDenseRatio N✶ n (n - r) :=
    UniformlyDenseRatio.dual N hE hRank hEcard hDense
  obtain ⟨σ, hσ⟩ :=
    hSolve N✶ (by omega) hn hDualE hDualRank hDualCard hDualDense
  refine ⟨σ, ?_⟩
  exact cyclicBasisOrder_of_dual N (n := n) (r := r) (s := n - r) hn (by omega) σ hσ

/-- KUM at `(r, n)` and KUM at `(n - r, n)` are equivalent. -/
theorem solvesKUMAtRankSize_dual_iff {r n : ℕ} (hrn : r < n) :
    SolvesKUMAtRankSize α (n - r) n ↔ SolvesKUMAtRankSize α r n := by
  refine ⟨SolvesKUMAtRankSize.of_dual hrn, fun h => ?_⟩
  intro N hr hn hE hRank hEcard hDense
  have hlt : n - r < n := by omega
  have h' : SolvesKUMAtRankSize α (n - (n - r)) n := by
    rw [Nat.sub_sub_self hrn.le]
    exact h
  exact SolvesKUMAtRankSize.of_dual hlt h' N hr hn hE hRank hEcard hDense

/-- KUM at rank `r` and size `r`: the ground set is a basis, so every ordering works. -/
theorem solvesKUMAtRankSize_self (r : ℕ) : SolvesKUMAtRankSize α r r := by
  intro N _hr hn hE hRank hEcard _hDense
  haveI : Finite N.E := hE.to_subtype
  have hncard : N.E.ncard = r := by
    have hcast : (N.E.ncard : ℕ∞) = r := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast
  let σ : Fin r ≃ N.E :=
    (Finite.equivFinOfCardEq (by simpa only [Nat.card_coe_set_eq] using hncard)).symm
  refine ⟨σ, fun i => ?_⟩
  have hsub : cyclicWindow r hn σ i ⊆ N.E := by
    rintro _ ⟨j, rfl⟩
    exact (σ _).2
  have hwin : (cyclicWindow r hn σ i).encard = (r : ℕ∞) := by
    rw [cyclicWindow, Function.Injective.encard_range]
    · simp
    · intro a b h
      have ha := a.2
      have hb := b.2
      have h2 := σ.injective (Subtype.ext h)
      exact Fin.ext (cyclicIndex_injective_offsets r hn i (by omega) (by omega) h2)
  have hEeq : cyclicWindow r hn σ i = N.E :=
    hE.eq_of_subset_of_encard_le' hsub (by rw [hwin, hEcard])
  rw [hEeq]
  have hind : N.Indep N.E := by
    rw [Matroid.indep_iff_eRk_eq_encard_of_finite hE, N.eRk_ground, hRank, hEcard]
  exact hind.isBase_of_eRk_ge hE (by rw [N.eRk_ground])

end

end HigherRankKUM
