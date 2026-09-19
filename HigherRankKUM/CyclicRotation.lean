import HigherRankKUM.CyclicOrder
import Mathlib.Tactic

namespace HigherRankKUM

noncomputable section

/-- Cyclic translation of the finite index set by a fixed offset. -/
def cyclicShiftEquiv (n : ℕ) (hn : 0 < n) (a : ℕ) : Fin n ≃ Fin n := by
  let f : Fin n → Fin n := fun i => cyclicIndex n hn i a
  apply Equiv.ofBijective f
  refine ⟨cyclicIndex_injective_start n hn a, ?_⟩
  exact Finite.surjective_of_injective (cyclicIndex_injective_start n hn a)

@[simp] theorem cyclicShiftEquiv_apply
    (n : ℕ) (hn : 0 < n) (a : ℕ) (i : Fin n) :
    cyclicShiftEquiv n hn a i = cyclicIndex n hn i a := by
  rfl

/-- Cyclic translation commutes with taking further cyclic offsets. -/
theorem cyclicShiftEquiv_cyclicIndex
    (n : ℕ) (hn : 0 < n) (a j : ℕ) (i : Fin n) :
    cyclicShiftEquiv n hn a (cyclicIndex n hn i j) =
      cyclicIndex n hn (cyclicShiftEquiv n hn a i) j := by
  simp only [cyclicShiftEquiv_apply]
  rw [cyclicIndex_add, cyclicIndex_add]
  simpa [Nat.add_comm]

/-- Precomposing an order by a cyclic translation simply translates the
starting point of every cyclic window. -/
theorem cyclicWindow_shift
    {α : Type*} {E : Set α} {n r : ℕ}
    (hn : 0 < n) (a : ℕ)
    (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow r hn ((cyclicShiftEquiv n hn a).trans σ) i =
      cyclicWindow r hn σ (cyclicShiftEquiv n hn a i) := by
  ext x
  simp only [cyclicWindow, Set.mem_range, Equiv.trans_apply]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    congr 1
    exact cyclicShiftEquiv_cyclicIndex n hn a j.val i
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    congr 1
    exact (cyclicShiftEquiv_cyclicIndex n hn a j.val i).symm

/-- A cyclic basis ordering remains one after a cyclic rotation. -/
theorem CyclicBasisOrder.shift
    {α : Type*} {M : Matroid α} {n r : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ M.E)
    (hσ : CyclicBasisOrder M r hn σ) (a : ℕ) :
    CyclicBasisOrder M r hn ((cyclicShiftEquiv n hn a).trans σ) := by
  intro i
  rw [cyclicWindow_shift]
  exact hσ (cyclicShiftEquiv n hn a i)

end

end HigherRankKUM
