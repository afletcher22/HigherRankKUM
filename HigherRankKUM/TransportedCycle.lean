import HigherRankKUM.CyclicOrder

namespace HigherRankKUM

open Set

noncomputable section

variable {α β : Type*}

/-- Transport cyclic indexing from `Fin n` across an arbitrary equivalence.
This is the adapter used to keep schedule proofs on symbolic position types
instead of repeatedly unfolding dependent `Fin` arithmetic. -/
def transportedCyclicIndex
    {n : ℕ} (hn : 0 < n)
    (e : Fin n ≃ β) (b : β) (d : ℕ) : β :=
  e (cyclicIndex n hn (e.symm b) d)

@[simp] theorem transportedCyclicIndex_apply
    {n : ℕ} (hn : 0 < n)
    (e : Fin n ≃ β) (i : Fin n) (d : ℕ) :
    transportedCyclicIndex hn e (e i) d =
      e (cyclicIndex n hn i d) := by
  simp [transportedCyclicIndex]

/-- A cyclic window expressed on a symbolic position type `β`, with the
cyclic structure transported from `Fin n` by `e`. -/
def transportedWindow
    {E : Set α} {n : ℕ}
    (r : ℕ) (hn : 0 < n)
    (e : Fin n ≃ β) (τ : β ≃ E) (b : β) : Set α :=
  Set.range fun j : Fin r =>
    (τ (transportedCyclicIndex hn e b j.val) : α)

/-- Composing a symbolic ground-set enumeration with its finite-position
adapter turns ordinary `cyclicWindow` into `transportedWindow`. -/
theorem cyclicWindow_trans_eq_transportedWindow
    {E : Set α} {n r : ℕ}
    (hn : 0 < n)
    (e : Fin n ≃ β) (τ : β ≃ E) (i : Fin n) :
    cyclicWindow r hn (e.trans τ) i =
      transportedWindow r hn e τ (e i) := by
  ext x
  simp [cyclicWindow, transportedWindow, transportedCyclicIndex]

/-- Prove a `CyclicBasisOrder` on symbolic schedule positions, then transport
it through a single finite-position adapter. -/
theorem cyclicBasisOrder_of_transport
    (M : Matroid α) {n r : ℕ}
    (hn : 0 < n)
    (e : Fin n ≃ β) (τ : β ≃ M.E)
    (hbase : ∀ b : β, M.IsBase (transportedWindow r hn e τ b)) :
    CyclicBasisOrder M r hn (e.trans τ) := by
  intro i
  rw [cyclicWindow_trans_eq_transportedWindow]
  exact hbase (e i)

end

end HigherRankKUM
