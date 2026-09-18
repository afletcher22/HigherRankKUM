import HigherRankKUM.DensitySlackDeletion
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

namespace HigherRankKUM

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- Maximum cardinality of a ground-set subset having rank exactly `j`.
If the rank layer is empty, the value is zero.

This is the `m_j` profile used in the density-slack deletion criterion. -/
def maxCardAtRank (M : Matroid α) [M.Finite] (j : ℕ) : ℕ :=
  ((M.ground_finite.toFinset.powerset.filter
      (fun S => M.eRk (S : Set α) = (j : ℕ∞))).sup Finset.card)

/-- Integer density slack
`s_j = n*j - r*m_j`, where `m_j` is the largest size of a rank-`j`
ground-set subset. -/
def deletionSlack (M : Matroid α) [M.Finite] (n r j : ℕ) : ℕ :=
  n * j - r * maxCardAtRank M j

theorem ncard_le_maxCardAtRank
    (M : Matroid α) [M.Finite] {j : ℕ} {X : Set α}
    (hX : X ⊆ M.E)
    (hRk : M.eRk X = (j : ℕ∞)) :
    X.ncard ≤ maxCardAtRank M j := by
  have hXfin : X.Finite := M.ground_finite.subset hX
  have hmem :
      hXfin.toFinset ∈
        M.ground_finite.toFinset.powerset.filter
          (fun S => M.eRk (S : Set α) = (j : ℕ∞)) := by
    simp only [Finset.mem_filter, Finset.mem_powerset,
      Set.Finite.coe_toFinset, Set.Finite.mem_toFinset]
    exact ⟨hX, hRk⟩
  have hle :=
    Finset.le_sup (f := Finset.card) hmem
  simpa [maxCardAtRank, Set.ncard_eq_toFinset_card X hXfin] using hle

/-- Every member of a rank layer satisfies a cardinality bound iff the
maximum cardinality of that layer does. Empty layers are handled by the
zero convention in `maxCardAtRank`. -/
theorem maxCardAtRank_le_iff
    (M : Matroid α) [M.Finite] (j B : ℕ) :
    maxCardAtRank M j ≤ B ↔
      ∀ X : Set α, X ⊆ M.E → M.eRk X = (j : ℕ∞) → X.ncard ≤ B := by
  constructor
  · intro h X hXE hRk
    exact (ncard_le_maxCardAtRank M hXE hRk).trans h
  · intro h
    unfold maxCardAtRank
    rw [Finset.sup_le_iff]
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    exact h (S : Set α) hS.1 hS.2

/-- The deletion-slack profile of a uniformly dense finite matroid never
underflows: `r*m_j ≤ n*j` in every rank layer. -/
theorem mul_maxCardAtRank_le_of_uniformlyDenseRatio
    (M : Matroid α) [M.Finite] (n r j : ℕ)
    (hDense : UniformlyDenseRatio M n r) :
    r * maxCardAtRank M j ≤ n * j := by
  let layer :=
    M.ground_finite.toFinset.powerset.filter
      (fun S => M.eRk (S : Set α) = (j : ℕ∞))
  by_cases hempty : layer = ∅
  · have hmzero : maxCardAtRank M j = 0 := by
      simp [maxCardAtRank, layer, hempty]
    simp [hmzero]
  · have hnonempty : layer.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨S, hSmem, hScard⟩ :=
      Finset.sup_mem_of_nonempty (f := Finset.card) hnonempty
    have hSfilter :
        S ∈ M.ground_finite.toFinset.powerset.filter
          (fun T => M.eRk (T : Set α) = (j : ℕ∞)) := by
      simpa [layer] using hSmem
    have hSsub : (S : Set α) ⊆ M.E := by
      simpa using (Finset.mem_filter.1 hSfilter).1
    have hSrk : M.eRk (S : Set α) = (j : ℕ∞) :=
      (Finset.mem_filter.1 hSfilter).2
    have hScardMax : S.card = maxCardAtRank M j := by
      simpa [maxCardAtRank, layer] using hScard
    have hd := hDense (S : Set α) hSsub
    rw [hSrk] at hd
    have hdNat : r * S.card ≤ n * j := by
      exact_mod_cast hd
    simpa [hScardMax] using hdNat

/-- Under uniform density, the slack inequality `j ≤ s_j` is equivalent
to the subtraction-free inequality `r*m_j + j ≤ n*j`. -/
theorem le_deletionSlack_iff
    (M : Matroid α) [M.Finite] (n r j : ℕ)
    (hDense : UniformlyDenseRatio M n r) :
    j ≤ deletionSlack M n r j ↔
      r * maxCardAtRank M j + j ≤ n * j := by
  unfold deletionSlack
  have hbase :=
    mul_maxCardAtRank_le_of_uniformlyDenseRatio M n r j hDense
  omega

/-- Subtraction-free exact universal deletion criterion.

For a finite matroid of positive rank `r) on `n>0` elements, every
single-element deletion satisfies the new density ratio `(n-1)/r` iff
every rank layer below `r` has enough integer slack:
`r*m_j + j ≤ n*j`.

This theorem itself does not assume the original matroid is uniformly dense;
that hypothesis is only needed to rewrite the condition as `s_j ≥ j`. -/
theorem all_deletions_uniformlyDenseRatio_iff_profile
    (M : Matroid α) [M.Finite] (n r : ℕ)
    (hn : 0 < n)
    (hr : 0 < r)
    (hRank : M.eRank = (r : ℕ∞))
    (hEcard : M.E.ncard = n) :
    (∀ e ∈ M.E,
      UniformlyDenseRatio (M ＼ ({e} : Set α)) (n - 1) r) ↔
      ∀ j : ℕ, j < r →
        r * maxCardAtRank M j + j ≤ n * j := by
  constructor
  · intro hdel j hjr
    let layer :=
      M.ground_finite.toFinset.powerset.filter
        (fun S => M.eRk (S : Set α) = (j : ℕ∞))
    by_cases hempty : layer = ∅
    · have hmzero : maxCardAtRank M j = 0 := by
        simp [maxCardAtRank, layer, hempty]
      rw [hmzero]
      have hjn : j ≤ n * j := by
        have : 1 ≤ n := hn
        nlinarith
      simpa using hjn
    · have hnonempty : layer.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨S, hSmem, hScard⟩ :=
        Finset.sup_mem_of_nonempty (f := Finset.card) hnonempty
      have hSfilter :
          S ∈ M.ground_finite.toFinset.powerset.filter
            (fun T => M.eRk (T : Set α) = (j : ℕ∞)) := by
        simpa [layer] using hSmem
      have hSsub : (S : Set α) ⊆ M.E := by
        simpa using (Finset.mem_filter.1 hSfilter).1
      have hSrk : M.eRk (S : Set α) = (j : ℕ∞) :=
        (Finset.mem_filter.1 hSfilter).2
      have hSne : (S : Set α) ≠ M.E := by
        intro hEq
        have hrEq : (j : ℕ∞) = (r : ℕ∞) := by
          calc
            (j : ℕ∞) = M.eRk (S : Set α) := hSrk.symm
            _ = M.eRk M.E := by rw [hEq]
            _ = M.eRank := M.eRank_def.symm
            _ = (r : ℕ∞) := hRank
        have : j = r := by exact_mod_cast hrEq
        omega
      obtain ⟨e, heE, heS⟩ := Set.exists_mem_not_mem_of_ne hSsub hSne
      have hSdel : (S : Set α) ⊆ (M ＼ ({e} : Set α)).E := by
        rw [Matroid.delete_ground]
        intro x hx
        exact ⟨hSsub hx, by
          simp only [Set.mem_singleton_iff]
          intro hxe
          exact heS (hxe ▸ hx)⟩
      have hd := hdel e heE (S : Set α) hSdel
      have hSrkDel :
          (M ＼ ({e} : Set α)).eRk (S : Set α) =
            M.eRk (S : Set α) := by
        have hSdiff : (S : Set α) ⊆ M.E \ ({e} : Set α) := by
          simpa [Matroid.delete_ground] using hSdel
        simpa [Matroid.delete_eq_restrict] using
          M.restrict_eRk_eq hSdiff
      have hScardMax : S.card = maxCardAtRank M j := by
        simpa [maxCardAtRank, layer] using hScard
      have hSNcard : (S : Set α).ncard = maxCardAtRank M j := by
        simp [Set.ncard_coe_Finset, hScardMax]
      rw [hSrkDel, hSrk, ← (M.ground_finite.subset hSsub).cast_ncard_eq,
        hSNcard] at hd
      have hdNat :
          r * maxCardAtRank M j ≤ (n - 1) * j := by
        exact_mod_cast hd
      omega
  · intro hprof e heE X hXdel
    have hXsub : X ⊆ M.E \ ({e} : Set α) := by
      simpa [Matroid.delete_ground] using hXdel
    have hXE : X ⊆ M.E := hXsub.trans Set.sdiff_subset
    have hXfin : X.Finite := M.ground_finite.subset hXE
    have hRkDel :
        (M ＼ ({e} : Set α)).eRk X = M.eRk X := by
      simpa [Matroid.delete_eq_restrict] using
        M.restrict_eRk_eq hXsub
    have hRkBound : M.eRk X ≤ (r : ℕ∞) := by
      rw [← hRank]
      exact M.eRk_le_eRank X
    obtain ⟨j, hRk, hjle⟩ := ENat.le_natCast_iff.mp hRkBound
    have hjleNat : j ≤ r := by exact_mod_cast hjle
    rw [hRkDel, hRk, ← hXfin.cast_ncard_eq]
    have hXEcard : M.E.ncard = n := hEcard
    have hDelCard :
        (M.E \ ({e} : Set α)).ncard = n - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem heE, hXEcard]
    by_cases hj : j < r
    · have hXm : X.ncard ≤ maxCardAtRank M j :=
        ncard_le_maxCardAtRank M hXE hRk
      have hp := hprof j hj
      have hNat :
          r * X.ncard ≤ (n - 1) * j := by
        have hm :
            r * X.ncard + j ≤ n * j := by
          calc
            r * X.ncard + j ≤
                r * maxCardAtRank M j + j := by
              gcongr
            _ ≤ n * j := hp
        omega
      exact_mod_cast hNat
    · have hjEq : j = r := by omega
      subst j
      have hXcard : X.ncard ≤ n - 1 := by
        calc
          X.ncard ≤ (M.E \ ({e} : Set α)).ncard :=
            Set.ncard_le_ncard hXsub M.ground_finite.sdiff
          _ = n - 1 := hDelCard
      have hNat : r * X.ncard ≤ (n - 1) * r :=
        Nat.mul_le_mul_left r hXcard
      exact_mod_cast hNat

/-- Exact arbitrary-rank deletion-slack criterion in the form used in the
research ledger.

For a finite uniformly dense matroid of positive rank `r) on `n>0`
elements, every deletion is uniformly dense at the new ratio `(n-1)/r`
iff `s_j ≥ j` for every nonzero rank layer `j<r`, where
`s_j = n*j - r*m_j`.

The `j=0` layer is automatic: uniform density forces its maximum
cardinality to be zero. -/
theorem all_deletions_uniformlyDenseRatio_iff_slack
    (M : Matroid α) [M.Finite] (n r : ℕ)
    (hn : 0 < n)
    (hr : 0 < r)
    (hRank : M.eRank = (r : ℕ∞))
    (hEcard : M.E.ncard = n)
    (hDense : UniformlyDenseRatio M n r) :
    (∀ e ∈ M.E,
      UniformlyDenseRatio (M ＼ ({e} : Set α)) (n - 1) r) ↔
      ∀ j : ℕ, 0 < j → j < r →
        j ≤ deletionSlack M n r j := by
  rw [all_deletions_uniformlyDenseRatio_iff_profile M n r hn hr hRank hEcard]
  constructor
  · intro hprof j hjpos hjr
    exact (le_deletionSlack_iff M n r j hDense).2 (hprof j hjr)
  · intro hslack j hjr
    by_cases hj0 : j = 0
    · subst j
      simp
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      exact (le_deletionSlack_iff M n r j hDense).1
        (hslack j hjpos hjr)

end

end HigherRankKUM
