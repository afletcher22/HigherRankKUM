import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Tactic

namespace HigherRankKUM

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
        ≤ (k : ℕ∞) * M.eRk (M.closure ({e} : Set α)) :=
      hDense (M.closure ({e} : Set α))
        (M.closure_subset_ground {e})
    _ = (k : ℕ∞) * M.eRk ({e} : Set α) := by
      rw [M.eRk_closure_eq]
    _ = (k : ℕ∞) * ({e} : Set α).encard := by
      rw [heNonloop.indep.eRk_eq_encard]
    _ = (k : ℕ∞) := by simp

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

end HigherRankKUM
