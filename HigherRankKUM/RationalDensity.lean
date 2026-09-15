import HigherRankKUM.TightContraction

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
Uniform density at the rational ratio `p/q`, written without division:
`q * |X| ≤ p * r(X)` for every ground-set subset `X`.

No coprimality assumption is built into the predicate; reducing `p/q` is an
arithmetic concern for later tight-set factorization lemmas.
-/
def UniformlyDenseRatio (M : Matroid α) (p q : ℕ) : Prop :=
  ∀ X : Set α, X ⊆ M.E →
    (q : ℕ∞) * X.encard ≤ (p : ℕ∞) * M.eRk X

/-- Equality in the cross-multiplied density bound. -/
def TightRatio (M : Matroid α) (p q : ℕ) (X : Set α) : Prop :=
  X ⊆ M.E ∧
    (q : ℕ∞) * X.encard = (p : ℕ∞) * M.eRk X

/-- The existing integer-density predicate is exactly the denominator-one case. -/
theorem uniformlyDenseRatio_one_iff
    (M : Matroid α) (k : ℕ) :
    UniformlyDenseRatio M k 1 ↔ UniformlyDense M k := by
  simp [UniformlyDenseRatio, UniformlyDense]

/-- The existing integer tightness predicate is the denominator-one case. -/
theorem tightRatio_one_iff
    (M : Matroid α) (k : ℕ) (X : Set α) :
    TightRatio M k 1 X ↔ Tight M k X := by
  simp [TightRatio, Tight]

/-- Rational uniform density is inherited by restriction. -/
theorem UniformlyDenseRatio.restrict
    (M : Matroid α) (p q : ℕ)
    (hDense : UniformlyDenseRatio M p q)
    {R : Set α} (hR : R ⊆ M.E) :
    UniformlyDenseRatio (M.restrict R) p q := by
  intro A hA
  have hAR : A ⊆ R := by
    simpa using hA
  have hAE : A ⊆ M.E := hAR.trans hR
  simpa [M.restrict_eRk_eq hAR] using hDense A hAE

/--
Rational uniform density is inherited by contraction of a finite tight set,
with the same numerator and denominator.
-/
theorem UniformlyDenseRatio.contract_tight
    (M : Matroid α) (p q : ℕ)
    (hDense : UniformlyDenseRatio M p q)
    {X : Set α}
    (hX : TightRatio M p q X)
    (hXfinite : X.Finite) :
    UniformlyDenseRatio (Matroid.contract M X) p q := by
  intro A hA
  have hAcomp : A ⊆ M.E \ X := by
    simpa using hA
  have hAXsubset : A ∪ X ⊆ M.E :=
    Set.union_subset (hAcomp.trans Set.sdiff_subset) hX.1
  have hdisjoint : Disjoint A X :=
    Set.disjoint_sdiff_left.mono_left hAcomp
  have hdense := hDense (A ∪ X) hAXsubset
  have hrank := eRk_union_eq_contract_eRk_add M hX.1 hA
  have hcancel : (q : ℕ∞) * X.encard ≠ ⊤ := by
    rw [← hXfinite.cast_ncard_eq, ← ENat.natCast_mul]
    exact ENat.natCast_ne_top _
  rw [Set.encard_union_eq hdisjoint, hrank,
    mul_add, mul_add, ← hX.2] at hdense
  exact (ENat.add_le_add_iff_right hcancel).mp hdense

/-- A finite rational-tight set produces restriction and contraction factors
with the same density ratio. -/
theorem UniformlyDenseRatio.tight_factors
    (M : Matroid α) (p q : ℕ)
    (hDense : UniformlyDenseRatio M p q)
    {X : Set α}
    (hX : TightRatio M p q X)
    (hXfinite : X.Finite) :
    UniformlyDenseRatio (Matroid.restrict M X) p q ∧
      UniformlyDenseRatio (Matroid.contract M X) p q := by
  exact ⟨UniformlyDenseRatio.restrict M p q hDense hX.1,
    UniformlyDenseRatio.contract_tight M p q hDense hX hXfinite⟩

end

end HigherRankKUM
