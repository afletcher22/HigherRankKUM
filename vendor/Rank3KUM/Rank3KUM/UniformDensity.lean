import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Tactic

namespace Rank3KUM

open Set

variable {α : Type*}

/-- Every ground-set subset satisfies `|X| ≤ k · r(X)`. -/
def UniformlyDense (M : Matroid α) (k : ℕ) : Prop :=
  ∀ X : Set α, X ⊆ M.E →
    X.encard ≤ (k : ℕ∞) * M.eRk X

/-- A ground-set subset is tight when equality holds in the density bound. -/
def Tight (M : Matroid α) (k : ℕ) (X : Set α) : Prop :=
  X ⊆ M.E ∧ X.encard = (k : ℕ∞) * M.eRk X


/-- Uniform density is inherited by restriction to a ground-set subset. -/
theorem UniformlyDense.restrict
    (M : Matroid α)
    (k : ℕ)
    (hDense : UniformlyDense M k)
    {R : Set α}
    (hR : R ⊆ M.E) :
    UniformlyDense (M.restrict R) k := by
  intro A hA
  have hAR : A ⊆ R := by
    simpa using hA
  have hAE : A ⊆ M.E :=
    hAR.trans hR
  simpa [M.restrict_eRk_eq hAR] using
    hDense A hAE

/-- In a loopless uniformly dense matroid, every parallel class has size at most `k`. -/
theorem closure_singleton_encard_le
    (M : Matroid α)
    (k : ℕ)
    (hDense : UniformlyDense M k)
    (hLoopless : M.Loopless)
    {e : α}
    (he : e ∈ M.E) :
    (M.closure ({e} : Set α)).encard ≤ (k : ℕ∞) := by
  let : M.Loopless := hLoopless
  have heNonloop : M.IsNonloop e :=
    Matroid.isNonloop_of_loopless he
  calc
    (M.closure ({e} : Set α)).encard
        ≤ (k : ℕ∞) *
            M.eRk (M.closure ({e} : Set α)) :=
      hDense (M.closure ({e} : Set α))
        (M.closure_subset_ground {e})
    _ = (k : ℕ∞) * M.eRk ({e} : Set α) := by
      rw [M.eRk_closure_eq]
    _ = (k : ℕ∞) * ({e} : Set α).encard := by
      rw [heNonloop.indep.eRk_eq_encard]
    _ = (k : ℕ∞) := by simp

#print axioms Rank3KUM.UniformlyDense.restrict
#print axioms Rank3KUM.closure_singleton_encard_le

/-- In a finite uniformly dense matroid, every tight set is a flat. -/
theorem tight_isFlat
    (M : Matroid α)
    (k : ℕ)
    (hE : M.E.Finite)
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X) :
    M.IsFlat X := by
  rw [Matroid.isFlat_iff_closure_eq]
  have hXfinite : X.Finite := hE.subset hX.1
  have hcard : (M.closure X).encard ≤ X.encard := by
    calc
      (M.closure X).encard
          ≤ (k : ℕ∞) * M.eRk (M.closure X) :=
        hDense (M.closure X) (M.closure_subset_ground X)
      _ = (k : ℕ∞) * M.eRk X := by
        rw [M.eRk_closure_eq]
      _ = X.encard := hX.2.symm
  exact
    (hXfinite.eq_of_subset_of_encard_le
      (M.subset_closure X hX.1) hcard).symm

/-- Uniform density excludes loops. -/
theorem loopless_of_uniformlyDense
    (M : Matroid α)
    (k : ℕ)
    (_hk : 0 < k)
    (hDense : UniformlyDense M k) :
    M.Loopless := by
  rw [Matroid.loopless_iff_forall_not_isLoop]
  intro e heE heLoop
  have hsingleton : ({e} : Set α) ⊆ M.E := by
    simpa using heE
  have h := hDense {e} hsingleton
  rw [Set.encard_singleton, heLoop.eRk_eq] at h
  simp at h

/--
A nonempty proper tight set in the stated rank-three situation has extended
rank exactly one or exactly two.
-/
theorem tight_rank_one_or_two
    (M : Matroid α)
    (k : ℕ)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (_hk : 0 < k)
    (_hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    M.eRk X = 1 ∨ M.eRk X = 2 := by
  have hXfinite : X.Finite := hE.subset hX.1

  have hr_ne_zero : M.eRk X ≠ 0 := by
    intro hr_zero
    have hencard_zero : X.encard = 0 := by
      rw [hX.2, hr_zero]
      simp
    exact hXnonempty.ne_empty
      (Set.encard_eq_zero.mp hencard_zero)

  have hr_ne_three : M.eRk X ≠ 3 := by
    intro hr_three
    have hcard_eq : X.encard = M.E.encard := by
      calc
        X.encard = (k : ℕ∞) * M.eRk X := hX.2
        _ = (k : ℕ∞) * 3 := by rw [hr_three]
        _ = ((k * 3 : ℕ) : ℕ∞) :=
          (ENat.natCast_mul k 3).symm
        _ = ((3 * k : ℕ) : ℕ∞) := by
          rw [Nat.mul_comm]
        _ = M.E.encard := hEcard.symm
    have hXE : X = M.E :=
      hXfinite.eq_of_subset_of_encard_le
        hX.1 hcard_eq.symm.le
    exact hXproper hXE

  have hr_le_three : M.eRk X ≤ 3 := by
    calc
      M.eRk X ≤ M.eRank := M.eRk_le_eRank X
      _ = 3 := hRank

  obtain ⟨n, hr_eq, hn⟩ :=
    ENat.le_natCast_iff.mp hr_le_three
  rw [hr_eq] at hr_ne_zero hr_ne_three ⊢
  interval_cases n <;> simp_all

/-- A tight rank-one set has cardinality `k`. -/
theorem tight_encard_eq_k_of_eRk_eq_one
    (M : Matroid α)
    (k : ℕ)
    {X : Set α}
    (hX : Tight M k X)
    (hr : M.eRk X = 1) :
    X.encard = (k : ℕ∞) := by
  calc
    X.encard = (k : ℕ∞) * M.eRk X := hX.2
    _ = (k : ℕ∞) * 1 := by rw [hr]
    _ = (k : ℕ∞) := by simp

/-- A tight rank-two set has cardinality `2k`. -/
theorem tight_encard_eq_two_mul_k_of_eRk_eq_two
    (M : Matroid α)
    (k : ℕ)
    {X : Set α}
    (hX : Tight M k X)
    (hr : M.eRk X = 2) :
    X.encard = ((2 * k : ℕ) : ℕ∞) := by
  calc
    X.encard = (k : ℕ∞) * M.eRk X := hX.2
    _ = (k : ℕ∞) * 2 := by rw [hr]
    _ = ((k * 2 : ℕ) : ℕ∞) :=
      (ENat.natCast_mul k 2).symm
    _ = ((2 * k : ℕ) : ℕ∞) := by
      rw [Nat.mul_comm]

/--
Every nonempty proper tight set in a finite uniformly dense rank-three matroid
on `3k` elements is a flat and has one of the two stated rank/cardinality types.
-/
theorem nonempty_proper_tight_flat_classification
    (M : Matroid α)
    (k : ℕ)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hk : 0 < k)
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    M.IsFlat X ∧
      ((M.eRk X = 1 ∧ X.encard = (k : ℕ∞)) ∨
       (M.eRk X = 2 ∧ X.encard = ((2 * k : ℕ) : ℕ∞))) := by
  refine ⟨tight_isFlat M k hE hDense hX, ?_⟩
  rcases
      tight_rank_one_or_two M k hE hRank hEcard hk hDense
        hX hXnonempty hXproper with hr_one | hr_two
  · exact Or.inl
      ⟨hr_one,
       tight_encard_eq_k_of_eRk_eq_one M k hX hr_one⟩
  · exact Or.inr
      ⟨hr_two,
       tight_encard_eq_two_mul_k_of_eRk_eq_two
         M k hX hr_two⟩

end Rank3KUM
