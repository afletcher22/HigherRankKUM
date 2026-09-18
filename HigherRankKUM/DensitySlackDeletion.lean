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


/-- In the strict integral setting with `k ≥ 2` and `|E| = kr`, no ground
element is a coloop. Equivalently, every single deletion preserves rank.

The proof is the density contradiction on `E \ {e}`: a coloop would make
that set nonspanning, hence rank at most `r-1`, but it still has `kr-1`
elements, which violates strict density. -/
theorem StrictlyUniformlyDenseRatio.not_isColoop_of_integral
    (M : Matroid α) (k r : ℕ)
    (hk : 2 ≤ k)
    (hr : 0 < r)
    (hE : M.E.Finite)
    (hRank : M.eRank = (r : ℕ∞))
    (hEcard : M.E.encard = ((k * r : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (k * r) r)
    {e : α} (he : e ∈ M.E) :
    ¬ M.IsColoop e := by
  intro hcol
  let X := M.E \ ({e} : Set α)
  have hXsub : X ⊆ M.E := by
    exact Set.sdiff_subset
  have hXfin : X.Finite :=
    hE.subset hXsub
  have hEn : M.E.ncard = k * r := by
    have h := hEcard
    rw [← hE.cast_ncard_eq] at h
    exact_mod_cast h
  have hXcard : X.ncard = k * r - 1 := by
    dsimp [X]
    rw [Set.ncard_sdiff_singleton_of_mem he hE, hEn]
  have hXnonempty : X.Nonempty := by
    rw [← Set.ncard_pos hXfin, hXcard]
    have hkr : 1 < k * r := by
      nlinarith
    omega
  have hXproper : X ≠ M.E := by
    intro hEq
    have heX : e ∈ X := by
      rw [hEq]
      exact he
    exact heX.2 (by simp)
  letI : M.Finite := ⟨hE⟩
  have hNotSpan : ¬ M.Spanning X := by
    simpa [X] using hcol.sdiff_not_spanning
  have hRankLt : M.eRk X < M.eRank := by
    have hnotle : ¬ M.eRank ≤ M.eRk X := by
      intro hle
      exact hNotSpan ((M.spanning_iff_eRk_le hXsub).2 hle)
    exact lt_of_not_ge hnotle
  rw [hRank] at hRankLt
  obtain ⟨j, hj, hjlt⟩ := ENat.lt_natCast_iff.mp hRankLt
  have hjltNat : j < r := by
    exact_mod_cast hjlt
  have hs := hStrict X hXsub hXnonempty hXproper
  rw [← hXfin.cast_ncard_eq, hj, hXcard] at hs
  have hsNat :
      r * (k * r - 1) < (k * r) * j := by
    exact_mod_cast hs
  have hUpper :
      (k * r) * j ≤ (k * r) * (r - 1) := by
    apply Nat.mul_le_mul_left
    omega
  have hbad :
      r * (k * r - 1) < (k * r) * (r - 1) :=
    hsNat.trans_le hUpper
  nlinarith

/-- KUM-facing arbitrary-rank deletion package for strict integral density.

For `k ≥ 2`, rank `r>0`, and `|E|=kr`, every ground-element deletion:
* has ground-set size `kr-1`,
* has the same rank `r`, and
* is uniformly dense at ratio `(kr-1)/r`.

Thus its size is automatically coprime to `r`; applying the external
van den Heuvel--Thomassé theorem is a separate literature step. -/
theorem StrictlyUniformlyDenseRatio.delete_integral_package
    (M : Matroid α) (k r : ℕ)
    (hk : 2 ≤ k)
    (hr : 0 < r)
    (hE : M.E.Finite)
    (hRank : M.eRank = (r : ℕ∞))
    (hEcard : M.E.encard = ((k * r : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (k * r) r)
    {e : α} (he : e ∈ M.E) :
    (M ＼ ({e} : Set α)).E.encard = ((k * r - 1 : ℕ) : ℕ∞) ∧
    (M ＼ ({e} : Set α)).eRank = (r : ℕ∞) ∧
    UniformlyDenseRatio (M ＼ ({e} : Set α)) (k * r - 1) r := by
  have hnotcol :=
    hStrict.not_isColoop_of_integral M k r hk hr hE hRank hEcard he
  have hspan : M.Spanning (M.E \ ({e} : Set α)) := by
    by_contra hnotspan
    exact hnotcol ((M.isColoop_iff_sdiff_not_spanning).2 hnotspan)
  have hdelRank :
      (M ＼ ({e} : Set α)).eRank = M.eRank := by
    simpa [Matroid.delete_eq_restrict] using hspan.eRank_restrict
  have hdelCard : (M ＼ ({e} : Set α)).E.encard =
      ((k * r - 1 : ℕ) : ℕ∞) := by
    rw [Matroid.delete_ground]
    have hEn : M.E.ncard = k * r := by
      have h := hEcard
      rw [← hE.cast_ncard_eq] at h
      exact_mod_cast h
    have hdiff :
        (M.E \ ({e} : Set α)).ncard = k * r - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem he hE, hEn]
    rw [← (hE.sdiff).cast_ncard_eq, hdiff]
  refine ⟨hdelCard, ?_, ?_⟩
  · simpa [hRank] using hdelRank
  · exact hStrict.delete_integral M k r hr hE hRank he

end

end HigherRankKUM
