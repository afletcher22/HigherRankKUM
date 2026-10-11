module

public import HigherRankKUMCert.Final

/-!
# Palomar solution

The same statement surface as `Challenge.lean`, proved from the rank-4 development
(`HigherRankKUM.solvesKUMAtRank_four`). The two definitions unfold to the project's
`UniformlyDenseRatio M |E| 4` and `CyclicBasisOrder M 4 hn σ`; the only translation is
`|E| = (M.E.ncard : ℕ∞)` for a finite ground set.
-/

@[expose] public section


namespace HigherRankKUM.Palomar

variable {α : Type*}

/-- Uniform density: `r(M) · |X| ≤ |E(M)| · r(X)` for every subset `X` of the ground set. -/
def UniformlyDense (M : Matroid α) : Prop :=
  ∀ X ⊆ M.E, M.eRank * X.encard ≤ M.E.encard * M.eRk X

/-- `σ` lists the ground set cyclically, and every `r` cyclically consecutive entries form a
basis. Position `i + j` is read modulo `n`. -/
def IsCyclicBasisOrdering (M : Matroid α) (r : ℕ) {n : ℕ} (hn : 0 < n) (σ : Fin n ≃ M.E) :
    Prop :=
  ∀ i : Fin n,
    M.IsBase (Set.range fun j : Fin r => (σ ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ : α))

/-- **The Kajitani–Ueno–Miyano conjecture in rank 4**: every finite uniformly dense matroid of
rank 4 has a cyclic basis ordering. -/
theorem rankFourKUM (M : Matroid α) (hfin : M.E.Finite) (hrank : M.eRank = 4)
    (hdense : UniformlyDense M) :
    ∃ (n : ℕ) (hn : 0 < n) (σ : Fin n ≃ M.E), IsCyclicBasisOrdering M 4 hn σ := by
  have hEcard : M.E.encard = (M.E.ncard : ℕ∞) := hfin.cast_ncard_eq.symm
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hBne : B.Nonempty := by
    rw [← Set.encard_pos, hB.encard_eq_eRank, hrank]
    exact_mod_cast (show (0 : ℕ) < 4 by norm_num)
  have hn : 0 < M.E.ncard := (Set.ncard_pos hfin).2 (hBne.mono hB.subset_ground)
  have hDense : UniformlyDenseRatio M M.E.ncard 4 := by
    intro X hX
    have h := hdense X hX
    rw [hrank, hEcard] at h
    exact_mod_cast h
  obtain ⟨σ, hσ⟩ := solvesKUMAtRank_four M.E.ncard M (by norm_num) hn hfin
    (by exact_mod_cast hrank) hEcard hDense
  exact ⟨M.E.ncard, hn, σ, hσ⟩

end HigherRankKUM.Palomar

#print axioms HigherRankKUM.Palomar.rankFourKUM
