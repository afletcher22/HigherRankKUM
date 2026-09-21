import HigherRankKUM.TightFactorReduction

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/-- Transport a generic cyclic basis ordering across an equality of ranks. -/
theorem exists_cyclicBasisOrder_congr_rank
    (M : Matroid α) {p q k : ℕ}
    (hpq : p = q)
    (hp : 0 < p) (hq : 0 < q) (hk : 0 < k)
    (hOrder : ∃ order : Fin (p * k) ≃ M.E,
      CyclicBasisOrder M p (Nat.mul_pos hp hk) order) :
    ∃ order : Fin (q * k) ≃ M.E,
      CyclicBasisOrder M q (Nat.mul_pos hq hk) order := by
  subst q
  simpa using hOrder

/-- Contracting a rank-`s` set from ambient rank `s+t` leaves rank `t`. -/
theorem contract_eRank_eq_of_eRank_eq_add
    (M : Matroid α) {X : Set α} {s t : ℕ}
    (hX : X ⊆ M.E)
    (hRank : M.eRank = ((s + t : ℕ) : ℕ∞))
    (hXrank : M.eRk X = s) :
    (Matroid.contract M X).eRank = t := by
  have hsum :
      (Matroid.contract M X).eRank + M.eRk X = M.eRank := by
    have h :=
      eRk_union_eq_contract_eRk_add
        M hX
          (show (Matroid.contract M X).E ⊆
            (Matroid.contract M X).E from Set.Subset.rfl)
    rw [(Matroid.contract M X).eRk_ground,
      Matroid.contract_ground,
      Set.sdiff_union_of_subset hX,
      M.eRk_ground] at h
    exact h.symm
  rw [hRank, hXrank] at hsum
  apply ENat.add_left_injective_of_ne_top
    (ENat.natCast_ne_top s)
  calc
    (Matroid.contract M X).eRank + (s : ℕ∞) =
        ((s + t : ℕ) : ℕ∞) := hsum
    _ = (t : ℕ∞) + (s : ℕ∞) := by
      rw [ENat.natCast_add, add_comm]

/--
Inductive tight-set reduction for divisible KUM.

If divisible KUM has already been solved at every positive rank below `r`,
then every finite uniformly dense rank-`r` instance on `r*k` elements that
has a nonempty proper tight set is cyclically basis-orderable. Thus, once all
lower ranks are known, genuinely new work at rank `r` is confined to the
strictly uniformly dense branch.
-/
theorem exists_cyclicBasisOrder_of_nonempty_proper_tight_of_lower_ranks
    (M : Matroid α) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = r)
    (hEcard : M.E.encard = ((r * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E)
    (hBelow : SolvesDivisibleKUMBelow α r) :
    ∃ order : Fin (r * k) ≃ M.E,
      CyclicBasisOrder M r (Nat.mul_pos hr hk) order := by
  have hXfinite : X.Finite := hE.subset hX.1
  have hrX_le : M.eRk X ≤ (r : ℕ∞) := by
    calc
      M.eRk X ≤ M.eRank := M.eRk_le_eRank X
      _ = r := hRank
  obtain ⟨s, hXrank, hs_le⟩ := ENat.le_natCast_iff.mp hrX_le
  have hs_ne_zero : s ≠ 0 := by
    intro hs0
    have hencard_zero : X.encard = 0 := by
      rw [hX.2, hXrank, hs0]
      simp
    exact hXnonempty.ne_empty
      (Set.encard_eq_zero.mp hencard_zero)
  have hs_ne_r : s ≠ r := by
    intro hsr
    have hcard_eq : X.encard = M.E.encard := by
      calc
        X.encard = (k : ℕ∞) * M.eRk X := hX.2
        _ = (k : ℕ∞) * s := by rw [hXrank]
        _ = ((k * s : ℕ) : ℕ∞) :=
          (ENat.natCast_mul k s).symm
        _ = ((r * k : ℕ) : ℕ∞) := by
          rw [hsr, Nat.mul_comm]
        _ = M.E.encard := hEcard.symm
    have hXE : X = M.E :=
      hXfinite.eq_of_subset_of_encard_le
        hX.1 hcard_eq.symm.le
    exact hXproper hXE
  have hs : 0 < s := by omega
  have hslt : s < r := by omega
  let t : ℕ := r - s
  have ht : 0 < t := by
    dsimp [t]
    omega
  have htlt : t < r := by
    dsimp [t]
    omega
  have hst : s + t = r := by
    dsimp [t]
    omega
  have hRankST : M.eRank = ((s + t : ℕ) : ℕ∞) := by
    calc
      M.eRank = (r : ℕ∞) := hRank
      _ = ((s + t : ℕ) : ℕ∞) := by rw [hst]
  have hEcardST :
      M.E.encard = (((s + t) * k : ℕ) : ℕ∞) := by
    calc
      M.E.encard = ((r * k : ℕ) : ℕ∞) := hEcard
      _ = (((s + t) * k : ℕ) : ℕ∞) := by rw [hst]
  have hContractRank : (Matroid.contract M X).eRank = t :=
    contract_eRank_eq_of_eRank_eq_add
      (M := M) (X := X) (s := s) (t := t)
      hX.1 hRankST hXrank
  have hSolveS : SolvesDivisibleKUMAtRank α s :=
    hBelow s hs hslt
  have hSolveT : SolvesDivisibleKUMAtRank α t :=
    hBelow t ht htlt
  have hOrder :=
    exists_cyclicBasisOrder_of_tight_of_rank_solutions
      (M := M) (X := X) (s := s) (t := t) (k := k)
      hs ht hk hE hEcardST hDense hX hXrank hContractRank
      hSolveS hSolveT
  exact
    exists_cyclicBasisOrder_congr_rank M hst
      (Nat.add_pos_left hs t) hr hk hOrder

end

end HigherRankKUM
