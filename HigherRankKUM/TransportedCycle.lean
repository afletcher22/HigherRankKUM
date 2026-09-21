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

@[simp] theorem transportedCyclicIndex_zero
    {n : ℕ} (hn : 0 < n)
    (e : Fin n ≃ β) (b : β) :
    transportedCyclicIndex hn e b 0 = b := by
  simp [transportedCyclicIndex]

theorem transportedCyclicIndex_add
    {n : ℕ} (hn : 0 < n)
    (e : Fin n ≃ β) (b : β) (a d : ℕ) :
    transportedCyclicIndex hn e
        (transportedCyclicIndex hn e b a) d =
      transportedCyclicIndex hn e b (a + d) := by
  simp [transportedCyclicIndex, cyclicIndex_add]

/-- One symbolic cyclic successor. -/
def transportedNext
    {n : ℕ} (hn : 0 < n)
    (e : Fin n ≃ β) (b : β) : β :=
  transportedCyclicIndex hn e b 1

@[simp] theorem transportedNext_apply
    {n : ℕ} (hn : 0 < n)
    (e : Fin n ≃ β) (i : Fin n) :
    transportedNext hn e (e i) =
      e (cyclicIndex n hn i 1) := by
  simp [transportedNext]

/-- A cyclic window expressed on a symbolic position type `β`, with the
cyclic structure transported from `Fin n` by `e`. -/
def transportedWindow
    {E : Set α} {n : ℕ}
    (r : ℕ) (hn : 0 < n)
    (e : Fin n ≃ β) (τ : β ≃ E) (b : β) : Set α :=
  Set.range fun j : Fin r =>
    (τ (transportedCyclicIndex hn e b j.val) : α)

/-- A symbolic four-window written without a quantified `Fin 4`.
This is the proof-facing form used by rank-four schedule constructions. -/
def transportedWindowFour
    {E : Set α} {n : ℕ}
    (hn : 0 < n)
    (e : Fin n ≃ β) (τ : β ≃ E) (b : β) : Set α :=
  {(τ (transportedCyclicIndex hn e b 0) : α),
    (τ (transportedCyclicIndex hn e b 1) : α),
    (τ (transportedCyclicIndex hn e b 2) : α),
    (τ (transportedCyclicIndex hn e b 3) : α)}

theorem transportedWindow_four_eq
    {E : Set α} {n : ℕ}
    (hn : 0 < n)
    (e : Fin n ≃ β) (τ : β ≃ E) (b : β) :
    transportedWindow 4 hn e τ b =
      transportedWindowFour hn e τ b := by
  ext x
  simp only [transportedWindow, transportedWindowFour, Set.mem_range,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · intro hx
    rcases hx with h | h | h | h
    · refine ⟨0, ?_⟩
      simpa using h.symm
    · refine ⟨1, ?_⟩
      simpa using h.symm
    · refine ⟨2, ?_⟩
      simpa using h.symm
    · refine ⟨3, ?_⟩
      simpa using h.symm

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
