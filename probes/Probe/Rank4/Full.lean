import Probe.ExtFinal
import Probe.Rank4.Kum10Chain
import HigherRankKUM.Rank4.SixElementBoundary
import Probe.Rank4.Hitting
import HigherRankKUM.Rank4.Unconditional
import HigherRankKUM.VHT.Theorem21

/-!
# Rank-4 KUM, given the hitting lemma

The proof is by strong induction on `n`:

* `n` odd: coprime KUM (van den Heuvel–Thomassé);
* `n = 4k`: Theorem D (`solvesDivisibleKUMAtRank_four'`);
* `n = 6`: duality with rank-2 KUM (`Rank4.exists_cyclicBasisOrder_of_rank_four_six`);
* `n = 10`: a van den Heuvel–Thomassé pair chain and one certificate (`Kum10Chain`);
* `n = 4k+2 ≥ 14`:
  * a nonempty proper tight set, or a dangerous plane: the Lean reductions of the main library;
  * otherwise `M` is strict with `t = 0`. The hitting lemma (`HittingLemma`, a hypothesis here)
    gives a basis `S` with `M \ S` uniformly dense on `4k - 2 ≥ 10` elements. By induction
    `M \ S` has a cyclic basis ordering, and the extension theorem X′ extends it to `M`.
-/

namespace HigherRankKUM

open Set
open scoped Matroid

/-- **The hitting lemma** for `k ≥ 3`: every strict rank-4 matroid on `4k+2` elements with no
dangerous hyperplane has a basis whose complement is uniformly dense. -/
def HittingLemma (α : Type*) : Prop :=
  ∀ (M : Matroid α) (k : ℕ), 3 ≤ k → Hitting.StrictT0 M k → ∃ S, Hitting.Deletable M k S

theorem coprime_four_of_mod {n : ℕ} (h : n % 4 = 1 ∨ n % 4 = 3) : Nat.Coprime 4 n := by
  rcases h with h | h <;> (rw [Nat.Coprime, Nat.gcd_rec, h] <;> decide)

theorem uniformlyDense_of_ratio_four {α : Type*} {M : Matroid α} {k : ℕ}
    (hDense : UniformlyDenseRatio M (4 * k) 4) : UniformlyDense M k := by
  rw [← uniformlyDenseRatio_one_iff]
  intro X hX
  have h := hDense X hX
  have h2 : ((4 : ℕ) : ℕ∞) * X.encard = 4 * (((1 : ℕ) : ℕ∞) * X.encard) := by
    push_cast
    ring
  have h3 : ((4 * k : ℕ) : ℕ∞) * M.eRk X = 4 * ((k : ℕ∞) * M.eRk X) := by
    push_cast
    ring
  rw [h2, h3] at h
  exact (ENat.mul_le_mul_left_iff (by norm_num) (by simp)).1 h

/-- **Rank-4 KUM**, given the hitting lemma. -/
theorem solvesKUMAtRank_four_of_hitting {α : Type*} (hhit : HittingLemma α) :
    SolvesKUMAtRank α 4 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hr hn hE hRank hEcard hDense
  have hRank4 : M.eRank = 4 := by simpa using hRank
  have hn4 : 4 ≤ n := by
    have h := M.eRk_le_encard M.E
    rw [M.eRk_ground, hRank4, hEcard] at h
    exact_mod_cast h
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with h0 | h1 | h2 | h3
  · -- `n = 4k`: Theorem D
    obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k := ⟨n / 4, by omega⟩
    exact exists_cyclicBasisOrder_congr M rfl rfl
      (solvesDivisibleKUMAtRank_four' M k hr (by omega) hE hRank hEcard
        (uniformlyDense_of_ratio_four hDense))
  · exact VHT.solvesKUMAtRankSize_of_coprime (coprime_four_of_mod (Or.inl h1)) M hr hn hE hRank
      hEcard hDense
  · -- `n = 4k+2`
    obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
    rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | hk3
    · exact Rank4.exists_cyclicBasisOrder_of_rank_four_six M hE hRank4
        (hEcard.trans (by norm_num)) hDense
    · exact solvesKUMAtRankSize_four_ten_of_pairChain M hr hn hE hRank hEcard hDense
    -- a nonempty proper tight set
    by_cases htight : ∃ X, TightRatio M (4 * k + 2) 4 X ∧ X.Nonempty ∧ X ≠ M.E
    · obtain ⟨X, hX, hne, hprop⟩ := htight
      exact exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight' M k hE hRank4
        hEcard hDense hX hne hprop
    have hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4 := fun X hX hne hprop =>
      lt_of_le_of_ne (hDense X hX) fun heq => htight ⟨X, ⟨hX, heq⟩, hne, hprop⟩
    -- a dangerous plane
    by_cases hdanger : ∃ H, Rank4GcdTwoDeletion.DangerousHyperplane M k H
    · obtain ⟨H, hH⟩ := hdanger
      exact Rank4DangerousBranches.exists_cbo_of_dangerous_hyperplane' (by omega) hE hRank4
        hEcard hStrict hH
    -- strict, `t = 0`: delete a deletable basis, order the rest, and extend
    have hT : Hitting.StrictT0 M k := ⟨hE, hRank4, hEcard, hStrict, fun H hH => hdanger ⟨H, hH⟩⟩
    obtain ⟨S, hSbase, hSdense⟩ := hhit M k hk3 hT
    have hSE : S ⊆ M.E := hSbase.subset_ground
    have hRE : M.E \ S ⊆ M.E := diff_subset
    have hRfin : (M.E \ S).Finite := hE.subset hRE
    have hScard : S.encard = 4 := by rw [hSbase.encard_eq_eRank, hRank4]
    have hRcard : (M.E \ S).encard = ((4 * k - 2 : ℕ) : ℕ∞) := by
      have h := Set.encard_sdiff_add_encard_of_subset hSE
      rw [hEcard, hScard, ← hRfin.cast_ncard_eq] at h
      rw [← hRfin.cast_ncard_eq]
      have h' : (M.E \ S).ncard + 4 = 4 * k + 2 := by exact_mod_cast h
      have h'' : (M.E \ S).ncard = 4 * k - 2 := by omega
      rw [h'']
    -- `M \ S` has rank 4
    obtain ⟨j, hj, hj4⟩ := hT.exists_eRk_eq (M.E \ S)
    have hj4' : 4 ≤ j := by
      have h := hSdense (M.E \ S) subset_rfl
      rw [Matroid.restrict_eRk_eq M subset_rfl, hj, hRcard] at h
      have h' : 4 * (4 * k - 2) ≤ (4 * k - 2) * j := by exact_mod_cast h
      have h'' : (4 * k - 2) * 4 ≤ (4 * k - 2) * j := by
        rw [Nat.mul_comm (4 * k - 2) 4]
        exact h'
      exact Nat.le_of_mul_le_mul_left h'' (by omega)
    have hrkR : M.eRk (M.E \ S) = M.eRank := by
      rw [hj, hRank4]
      exact_mod_cast (show j = 4 by omega)
    have hRank' : (M ↾ (M.E \ S)).eRank = ((4 : ℕ) : ℕ∞) := by
      rw [← Matroid.eRk_ground, Matroid.restrict_ground_eq, Matroid.restrict_eRk_eq _ subset_rfl, hj]
      exact_mod_cast (show j = 4 by omega)
    obtain ⟨σ, hσ⟩ := ih (4 * k - 2) (by omega) (M ↾ (M.E \ S)) hr (by omega) hRfin hRank'
      hRcard hSdense
    have hcbo : CyclicBasisOrder M 4 (by omega) σ := fun i =>
      isBase_of_isBase_restrict hRE (hσ i) hrkR (Set.finite_range _)
    have hext : Rank4Extension α (4 * k - 2) := by
      rcases Nat.lt_or_ge k 4 with hk4 | hk4
      · have hk : k = 3 := by omega
        subst hk
        exact rank4Extension_ten
      · exact rank4Extension_of_fourteen_le (by omega)
    obtain ⟨τ, hτ⟩ := hext M S (by omega) hE hRank4 hSbase ⟨σ, hcbo⟩
    exact exists_cyclicBasisOrder_congr M (by omega) rfl ⟨τ, hτ⟩
  · exact VHT.solvesKUMAtRankSize_of_coprime (coprime_four_of_mod (Or.inr h3)) M hr hn hE hRank
      hEcard hDense

#print axioms solvesKUMAtRank_four_of_hitting

end HigherRankKUM
