module

public import HigherRankKUM.SAT.EncBridge

/-!
# Bitmask ranks and numberings

Helpers shared by the certificate bridges: a numbering of a finite set of known size, the rank of
the set named by a bitmask (`maskRank`), and the fact that a cyclic window of rank `4` in a rank-4
matroid is a basis.
-/

@[expose] public section


namespace HigherRankKUM.SAT

open Set HigherRankKUM
open scoped Matroid

variable {α : Type*}

/-- A numbering of a finite set of known size. -/
noncomputable def finEquivOfSetEncard {S : Set α} {n : ℕ} (hS : S.Finite)
    (h : S.encard = (n : ℕ∞)) : Fin n ≃ S := by
  haveI : Finite S := hS.to_subtype
  have hn : S.ncard = n := by
    have hcast : (S.ncard : ℕ∞) = n := by
      rw [hS.cast_ncard_eq]
      exact h
    exact_mod_cast hcast
  exact (Finite.equivFinOfCardEq (by simpa only [Nat.card_coe_set_eq] using hn)).symm

/-- The rank in `M` of the set named by the bitmask `X`. -/
noncomputable def maskRank (M : Matroid α) {m : ℕ} (pos : Fin m ≃ M.E) (X : ℕ) : ℕ :=
  (M.eRk (maskSet pos X)).toNat

theorem maskRank_cast {M : Matroid α} (hRank : M.eRank = 4) {m : ℕ} (pos : Fin m ≃ M.E)
    (X : ℕ) : ((maskRank M pos X : ℕ) : ℕ∞) = M.eRk (maskSet pos X) :=
  ENat.coe_toNat (ne_top_of_le_ne_top (by rw [hRank]; exact ENat.coe_ne_top 4)
    (M.eRk_le_eRank _))

theorem four_le_maskRank {M : Matroid α} (hRank : M.eRank = 4) {m : ℕ} (pos : Fin m ≃ M.E)
    {X : ℕ} {B : Set α} (hB : B ⊆ maskSet pos X) (hBase : M.IsBase B) :
    4 ≤ maskRank M pos X := by
  have h := M.eRk_mono hB
  rw [hBase.indep.eRk_eq_encard, hBase.encard_eq_eRank, hRank, ← maskRank_cast hRank pos X] at h
  exact_mod_cast h

/-- A cyclic window of rank at least `4` in a rank-4 matroid is a basis. -/
theorem isBase_cyclicWindow_of_four_le {M : Matroid α} (hRank : M.eRank = 4) {n : ℕ}
    (hn : 0 < n) (τ : Fin n ≃ M.E) (j : Fin n)
    (h4 : (4 : ℕ∞) ≤ M.eRk (cyclicWindow 4 hn τ j)) : M.IsBase (cyclicWindow 4 hn τ j) := by
  have hWfin : (cyclicWindow 4 hn τ j).Finite := Set.finite_range _
  have hWcard : (cyclicWindow 4 hn τ j).encard ≤ 4 := by
    rw [cyclicWindow, ← Set.image_univ]
    exact (Set.encard_image_le _ _).trans (by simp)
  have hind : M.Indep (cyclicWindow 4 hn τ j) :=
    (Matroid.indep_iff_eRk_eq_encard_of_finite (M := M) hWfin).2
      (le_antisymm (M.eRk_le_encard _) (hWcard.trans h4))
  exact hind.isBase_of_eRk_ge hWfin (by rw [hRank]; exact h4)

end HigherRankKUM.SAT
