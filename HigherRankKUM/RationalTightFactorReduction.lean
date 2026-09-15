import HigherRankKUM.PeriodicGluing
import HigherRankKUM.FullSolver
import HigherRankKUM.TightInduction

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
Rational tight-factor reduction with the rank factorization made explicit.

The ambient instance has size `(a+b)*p` and rank `(a+b)*q`. A finite tight
set of rank `a*q` therefore has size `a*p`; its contraction has size `b*p`
and rank `b*q`. If full KUM is available at those two factor ranks, the
periodic density-free gluing theorem produces a cyclic basis order of `M`.
-/
theorem exists_cyclicBasisOrder_of_ratio_tight_of_rank_solutions
    (M : Matroid α) {X : Set α} {a b p q : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q)
    (hE : M.E.Finite)
    (hEcard : M.E.encard = (((a + b) * p : ℕ) : ℕ∞))
    (hRank : M.eRank = (((a + b) * q : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M p q)
    (hX : TightRatio M p q X)
    (hXrank : M.eRk X = ((a * q : ℕ) : ℕ∞))
    (hSolveL : SolvesKUMAtRank α (a * q))
    (hSolveR : SolvesKUMAtRank α (b * q)) :
    ∃ order : Fin ((a + b) * p) ≃ M.E,
      CyclicBasisOrder M ((a + b) * q)
        (Nat.mul_pos (by omega) hp) order := by
  have hXfinite : X.Finite := hE.subset hX.1
  have hComplementFinite : (M.E \ X).Finite :=
    hE.subset Set.sdiff_subset
  have hXcard0 :=
    TightRatio.encard_eq_mul_of_eRk_eq_mul
      M p q a hq hXfinite hX (by
        simpa [Nat.mul_comm] using hXrank)
  have hXcard : X.encard = ((a * p : ℕ) : ℕ∞) := by
    simpa [Nat.mul_comm] using hXcard0
  have hsum :
      X.encard + (M.E \ X).encard = M.E.encard := by
    rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
      Set.union_sdiff_cancel hX.1]
  have hComplementCard :
      (M.E \ X).encard = ((b * p : ℕ) : ℕ∞) := by
    apply ENat.add_right_injective_of_ne_top
      (ENat.natCast_ne_top (a * p))
    calc
      ((a * p : ℕ) : ℕ∞) + (M.E \ X).encard =
          X.encard + (M.E \ X).encard := by rw [hXcard]
      _ = M.E.encard := hsum
      _ = (((a + b) * p : ℕ) : ℕ∞) := hEcard
      _ = ((a * p : ℕ) : ℕ∞) + ((b * p : ℕ) : ℕ∞) := by
        rw [Nat.add_mul, ENat.natCast_add]
  have hRestrictFinite : (Matroid.restrict M X).E.Finite := by
    simpa [Matroid.restrict_ground_eq] using hXfinite
  have hContractFinite : (Matroid.contract M X).E.Finite := by
    simpa [Matroid.contract_ground] using hComplementFinite
  have hRestrictRank :
      (Matroid.restrict M X).eRank = (a * q : ℕ) := by
    rw [Matroid.eRank_def, Matroid.restrict_ground_eq,
      M.restrict_eRk_eq Set.Subset.rfl, hXrank]
  have hRestrictCard :
      (Matroid.restrict M X).E.encard = ((a * p : ℕ) : ℕ∞) := by
    simpa [Matroid.restrict_ground_eq] using hXcard
  have hRankAB : M.eRank = (((a * q) + (b * q) : ℕ) : ℕ∞) := by
    calc
      M.eRank = (((a + b) * q : ℕ) : ℕ∞) := hRank
      _ = (((a * q) + (b * q) : ℕ) : ℕ∞) := by rw [Nat.add_mul]
  have hContractRank :
      (Matroid.contract M X).eRank = (b * q : ℕ) :=
    contract_eRank_eq_of_eRank_eq_add
      (M := M) (X := X) (s := a * q) (t := b * q)
      hX.1 hRankAB hXrank
  have hContractCard :
      (Matroid.contract M X).E.encard = ((b * p : ℕ) : ℕ∞) := by
    simpa [Matroid.contract_ground] using hComplementCard
  obtain ⟨hRestrictDense0, hContractDense0⟩ :=
    UniformlyDenseRatio.tight_factors M p q hDense hX hXfinite
  have hRestrictDense :
      UniformlyDenseRatio (Matroid.restrict M X) (a * p) (a * q) :=
    UniformlyDenseRatio.scale
      (Matroid.restrict M X) p q a hRestrictDense0
  have hContractDense :
      UniformlyDenseRatio (Matroid.contract M X) (b * p) (b * q) :=
    UniformlyDenseRatio.scale
      (Matroid.contract M X) p q b hContractDense0
  obtain ⟨σL, hL⟩ :=
    hSolveL (Matroid.restrict M X) (a * p)
      (Nat.mul_pos ha hq) (Nat.mul_pos ha hp)
      hRestrictFinite hRestrictRank hRestrictCard hRestrictDense
  obtain ⟨σR, hR⟩ :=
    hSolveR (Matroid.contract M X) (b * p)
      (Nat.mul_pos hb hq) (Nat.mul_pos hb hp)
      hContractFinite hContractRank hContractCard hContractDense
  exact
    exists_cyclicBasisOrder_of_periodic_restrict_contract
      M ha hb hp hX.1 σL σR hL hR

end

end HigherRankKUM
