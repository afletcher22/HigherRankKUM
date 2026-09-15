import HigherRankKUM.AdmissiblePairCycle
import Mathlib.Data.Set.Card

namespace HigherRankKUM
namespace AdmissiblePairCycle.Data

open Set
open PairCycleIndexing

variable {α : Type*} {M : Matroid α} {N h : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N h hN)

/-- The coordinate map defining the middle core is injective in the
nontrivial range `0 < h < N`. -/
theorem core_coordinate_injective
    (hh : 0 < h) (hhN : h < N) (i : Fin N) :
    Function.Injective
      (fun z : Fin (h - 1) × Bool =>
        A.element (cyclicIndex N hN i (z.1.val + 1)) z.2) := by
  intro z w hzw
  have hp :
      (cyclicIndex N hN i (z.1.val + 1), z.2) =
        (cyclicIndex N hN i (w.1.val + 1), w.2) :=
    A.element_injective hzw
  have hi := congrArg Prod.fst hp
  have hb := congrArg Prod.snd hp
  have hoffz : z.1.val + 1 < N := by omega
  have hoffw : w.1.val + 1 < N := by omega
  have ho := cyclicIndex_injective_offsets N hN i hoffz hoffw hi
  apply Prod.ext
  · apply Fin.ext
    omega
  · exact hb

/-- The middle core contains exactly `2h-2` elements. -/
theorem core_encard
    (hh : 0 < h) (hhN : h < N) (i : Fin N) :
    (A.core i).encard = ((2 * h - 2 : ℕ) : ℕ∞) := by
  have hf := A.core_coordinate_injective hh hhN i
  rw [AdmissiblePairCycle.Data.core, ← Set.image_univ, hf.encard_image]
  simp only [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  have hnat : (h - 1) * 2 = 2 * h - 2 := by omega
  exact congrArg (fun n : ℕ => (n : ℕ∞)) hnat

end AdmissiblePairCycle.Data
end HigherRankKUM
