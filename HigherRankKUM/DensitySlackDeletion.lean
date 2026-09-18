import HigherRankKUM.StrictDensity
import Mathlib.Combinatorics.Matroid.Minor.Delete

namespace HigherRankKUM

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- Arbitrary-rank strict integral deletion theorem.

If `M` has finite ground set, rank `r>0`, and is strictly uniformly dense
at the integral density `k = |E|/r` (written as the ratio `kr/r`), then
deleting any ground element preserves uniform density at the new ratio
`(kr-1)/r`.

The ground-set cardinality equality `|E|=kr` is not needed for the density
inequality itself; callers use it separately to identify the new KUM size.
-/
theorem StrictlyUniformlyDenseRatio.delete_integral
    (M : Matroid α) (k r : ℕ)
    (hr : 0 < r)
    (hE : M.E.Finite)
    (hRank : M.eRank = (r : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (k * r) r)
    {e : α} (he : e ∈ M.E) :
    UniformlyDenseRatio (M ＼ ({e} : Set α)) (k * r - 1) r := by
  intro X hXdel
  have hXsub : X ⊆ M.E \ ({e} : Set α) := by
    simpa [Matroid.delete_ground] using hXdel
  have hXE : X ⊆ M.E :=
    hXsub.trans Set.sdiff_subset
  have heX : e ∉ X := by
    intro heMem
    exact (hXsub heMem).2 (by simp)
  have hXfin : X.Finite :=
    hE.subset hXE
  have hDeleteRank :
      (M ＼ ({e} : Set α)).eRk X = M.eRk X := by
    simpa [Matroid.delete_eq_restrict] using
      M.restrict_eRk_eq hXsub
  by_cases hXempty : X = ∅
  · subst X
    simp
  have hXnonempty : X.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hXempty
  have hXproper : X ≠ M.E := by
    intro hEq
    have : e ∈ X := by
      rw [hEq]
      exact he
    exact heX this
  have hRk : M.eRk X ≤ (r : ℕ∞) := by
    rw [← hRank]
    exact M.eRk_le_eRank X
  obtain ⟨j, hj, hjle⟩ := ENat.le_natCast_iff.mp hRk
  have hjleNat : j ≤ r := by
    exact_mod_cast hjle
  have hs := hStrict X hXE hXnonempty hXproper
  rw [← hXfin.cast_ncard_eq, hj] at hs
  have hsNat : r * X.ncard < (k * r) * j := by
    exact_mod_cast hs
  have hsNat' : r * X.ncard < r * (k * j) := by
    calc
      r * X.ncard < (k * r) * j := hsNat
      _ = r * (k * j) := by ring
  have hcardLt : X.ncard < k * j :=
    (Nat.mul_lt_mul_left hr).mp hsNat'
  have hcardSucc : X.ncard + 1 ≤ k * j := by
    omega
  have hmul :
      r * X.ncard + r ≤ r * (k * j) := by
    calc
      r * X.ncard + r = r * (X.ncard + 1) := by ring
      _ ≤ r * (k * j) := Nat.mul_le_mul_left r hcardSucc
  have hwithJ :
      r * X.ncard + j ≤ (k * r) * j := by
    calc
      r * X.ncard + j ≤ r * X.ncard + r := Nat.add_le_add_left hjleNat _
      _ ≤ r * (k * j) := hmul
      _ = (k * r) * j := by ring
  have htargetNat :
      r * X.ncard ≤ (k * r - 1) * j := by
    rw [Nat.sub_mul]
    simp only [one_mul]
    omega
  rw [hDeleteRank, ← hXfin.cast_ncard_eq, hj]
  exact_mod_cast htargetNat

end

end HigherRankKUM
