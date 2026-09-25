import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# Draft Palomar challenge: the Kajitani–Ueno–Miyano conjecture in rank 4

Statement file only; Palomar allows `sorry` in the challenge module.  It imports Mathlib only.

A matroid `M` with ground set `E` is *uniformly dense* if `r(M) · |X| ≤ |E| · r(X)` for every
`X ⊆ E`.  A *cyclic basis ordering* is a cyclic ordering of `E` in which every `r(M)` cyclically
consecutive elements form a basis.  Kajitani, Ueno and Miyano (1988) conjectured that every
uniformly dense matroid has one.  This file states the conjecture for matroids of rank 4.

The definitions unfold to `HigherRankKUM.UniformlyDenseRatio M |E| 4` and
`HigherRankKUM.CyclicBasisOrder M 4 hn σ`, so the solution needs no translation lemmas beyond
unfolding.
-/

namespace KUM

variable {α : Type*}

/-- Uniform density: `r(M) · |X| ≤ |E(M)| · r(X)` for every subset `X` of the ground set. -/
def UniformlyDense (M : Matroid α) : Prop :=
  ∀ X ⊆ M.E, M.eRank * X.encard ≤ M.E.encard * M.eRk X

/-- `σ` lists the ground set cyclically, and every `r` cyclically consecutive entries form a
basis.  Position `i + j` is read modulo `n`. -/
def IsCyclicBasisOrdering (M : Matroid α) (r : ℕ) {n : ℕ} (hn : 0 < n) (σ : Fin n ≃ M.E) :
    Prop :=
  ∀ i : Fin n,
    M.IsBase (Set.range fun j : Fin r => (σ ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ : α))

/-- The Kajitani–Ueno–Miyano conjecture for matroids of rank 4: every finite uniformly dense
matroid of rank 4 has a cyclic basis ordering. -/
theorem kum_rank_four (M : Matroid α) (hfin : M.E.Finite) (hrank : M.eRank = 4)
    (hdense : UniformlyDense M) :
    ∃ (n : ℕ) (hn : 0 < n) (σ : Fin n ≃ M.E), IsCyclicBasisOrdering M 4 hn σ := by
  sorry

end KUM
