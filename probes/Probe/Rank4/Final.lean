import Probe.Rank4.Full
import Probe.Rank4.LemmaH
import Probe.Rank4.HitGeFour
import Probe.EncHBridgeG
import Probe.Hit14Line
import Probe.Hit14G
import HigherRankKUM.VHT.Covers

/-!
# Rank-4 KUM

The hitting lemma (`HittingLemma`) comes from:

* for `k ≥ 4`, Lemma U applied to a double cover from van den Heuvel–Thomassé;
* for `k = 3`, one of three cases:
  * a 9-element plane: the `hit14g` certificate;
  * a 6-element line and no 9-element plane: the `hit14line` certificate;
  * neither: Lemma H.

Together with `solvesKUMAtRank_four_of_hitting`, it gives rank-4 KUM.
-/

namespace HigherRankKUM

open Set Probe.Enc
open scoped Matroid

/-- The hitting lemma at `k = 3`. -/
theorem hitting_three {α : Type*} (M : Matroid α) (hT : Hitting.StrictT0 M 3) :
    ∃ S, Hitting.Deletable M 3 S := by
  by_cases h9 : ∃ K, M.IsFlat K ∧ M.eRk K = 3 ∧ K.encard = ((3 * 3 : ℕ) : ℕ∞)
  · obtain ⟨K, hKflat, hKrank, hKcard⟩ := h9
    exact deletable_of_hitG Hit14G.no_model hT hKflat.subset_ground hKrank hKcard
  push_neg at h9
  by_cases h6 : ∃ L, M.IsFlat L ∧ M.eRk L = 2 ∧ L.encard = ((2 * 3 : ℕ) : ℕ∞)
  · obtain ⟨L, hLflat, hLrank, hLcard⟩ := h6
    exact deletable_of_hitLine Hit14Line.no_model hT hLflat.subset_ground hLrank hLcard h9
  push_neg at h6
  obtain ⟨S, hS, hD⟩ := Hitting.lemmaH M 3 (by norm_num) hT h9 h6
  exact ⟨S, Hitting.deletable_of_meetsDemands hT (by norm_num) hS hD⟩

/-- **The hitting lemma** for every `k ≥ 3`. -/
theorem hittingLemma {α : Type*} : HittingLemma α := by
  intro M k hk hT
  rcases Nat.lt_or_ge k 4 with h | h
  · have hk3 : k = 3 := by omega
    subst hk3
    exact hitting_three M hT
  · exact hitting_ge_four M h hT

/-- **Rank-4 KUM**: every uniformly dense rank-4 matroid has a cyclic basis ordering. -/
theorem solvesKUMAtRank_four {α : Type*} : SolvesKUMAtRank α 4 :=
  solvesKUMAtRank_four_of_hitting hittingLemma

#print axioms solvesKUMAtRank_four

end HigherRankKUM
