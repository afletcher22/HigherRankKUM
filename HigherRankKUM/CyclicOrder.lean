import HigherRankKUM.CyclicIndex
import Mathlib.Combinatorics.Matroid.Dual
import Mathlib.Tactic

namespace HigherRankKUM

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- The set of `r` cyclically consecutive entries beginning at `i`. -/
def cyclicWindow
    {E : Set α} {n : ℕ}
    (r : ℕ) (hn : 0 < n)
    (σ : Fin n ≃ E) (i : Fin n) : Set α :=
  Set.range fun j : Fin r =>
    (σ (cyclicIndex n hn i j.val) : α)

/--
If `n = r + s`, the length-`r` window beginning at `i` together with
the length-`s` window beginning `r` steps later covers the whole cycle.
-/
theorem cyclicWindow_union_shifted
    {E : Set α} {n r s : ℕ}
    (hn : 0 < n) (hrs : n = r + s)
    (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow r hn σ i ∪
        cyclicWindow s hn σ (cyclicIndex n hn i r) = E := by
  ext x
  simp only [cyclicWindow, Set.mem_union, Set.mem_range]
  constructor
  · rintro (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact (σ _).property
    · exact (σ _).property
  · intro hxE
    let q : Fin n := σ.symm ⟨x, hxE⟩
    have hqx : (σ q : α) = x := by
      simpa [q] using
        congrArg Subtype.val (σ.apply_symm_apply ⟨x, hxE⟩)
    obtain ⟨t, ht, _⟩ := existsUnique_cyclicIndex_offset n hn i q
    by_cases htr : t.val < r
    · left
      refine ⟨⟨t.val, htr⟩, ?_⟩
      change (σ (cyclicIndex n hn i t.val) : α) = x
      rw [← ht]
      exact hqx
    · right
      have hbs : t.val - r < s := by omega
      let b : Fin s := ⟨t.val - r, hbs⟩
      refine ⟨b, ?_⟩
      change
        (σ (cyclicIndex n hn (cyclicIndex n hn i r) b.val) : α) = x
      rw [cyclicIndex_add]
      have hsplit : r + b.val = t.val := by
        dsimp [b]
        omega
      rw [hsplit, ← ht]
      exact hqx

/--
The two complementary cyclic windows in a cycle of length `r+s` are
disjoint.
-/
theorem cyclicWindow_disjoint_shifted
    {E : Set α} {n r s : ℕ}
    (hn : 0 < n) (hrs : n = r + s)
    (σ : Fin n ≃ E) (i : Fin n) :
    Disjoint (cyclicWindow r hn σ i)
      (cyclicWindow s hn σ (cyclicIndex n hn i r)) := by
  rw [Set.disjoint_left]
  intro x hxR hxS
  simp only [cyclicWindow, Set.mem_range] at hxR hxS
  rcases hxR with ⟨a, ha⟩
  rcases hxS with ⟨b, hb⟩
  have hidx :
      cyclicIndex n hn i a.val =
        cyclicIndex n hn (cyclicIndex n hn i r) b.val := by
    apply σ.injective
    apply Subtype.ext
    exact ha.trans hb.symm
  rw [cyclicIndex_add] at hidx
  have haN : a.val < n := by omega
  have hbN : r + b.val < n := by omega
  have hab :
      a.val = r + b.val :=
    cyclicIndex_injective_offsets n hn i haN hbN hidx
  omega

/--
For `n = r+s`, the complement in the enumerated ground set of the
length-`s` window starting `r` steps after `i` is exactly the
length-`r` window starting at `i`.
-/
theorem sdiff_shifted_cyclicWindow_eq
    {E : Set α} {n r s : ℕ}
    (hn : 0 < n) (hrs : n = r + s)
    (σ : Fin n ≃ E) (i : Fin n) :
    E \ cyclicWindow s hn σ (cyclicIndex n hn i r) =
      cyclicWindow r hn σ i := by
  have hunion := cyclicWindow_union_shifted hn hrs σ i
  have hdisj := cyclicWindow_disjoint_shifted hn hrs σ i
  ext x
  simp only [Set.mem_sdiff]
  constructor
  · rintro ⟨hxE, hxNotS⟩
    have hxU :
        x ∈ cyclicWindow r hn σ i ∪
          cyclicWindow s hn σ (cyclicIndex n hn i r) := by
      rw [hunion]
      exact hxE
    rcases hxU with hxR | hxS
    · exact hxR
    · exact (hxNotS hxS).elim
  · intro hxR
    refine ⟨?_, ?_⟩
    · have hxU :
          x ∈ cyclicWindow r hn σ i ∪
            cyclicWindow s hn σ (cyclicIndex n hn i r) :=
        Or.inl hxR
      rw [hunion] at hxU
      exact hxU
    · exact (Set.disjoint_left.mp hdisj) hxR

/-- An arbitrary-rank cyclic basis ordering. -/
def CyclicBasisOrder
    (M : Matroid α) (r : ℕ)
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) : Prop :=
  ∀ i : Fin n, M.IsBase (cyclicWindow r hn σ i)

/--
A cyclic basis ordering of the dual by the complementary window size gives
a cyclic basis ordering of the original matroid on the same cyclic order.
-/
theorem cyclicBasisOrder_of_dual
    (M : Matroid α) {n r s : ℕ}
    (hn : 0 < n) (hrs : n = r + s)
    (σ : Fin n ≃ M.E)
    (hDual : CyclicBasisOrder M✶ s hn σ) :
    CyclicBasisOrder M r hn σ := by
  intro i
  have hBdual :
      M✶.IsBase
        (cyclicWindow s hn σ (cyclicIndex n hn i r)) :=
    hDual (cyclicIndex n hn i r)
  have hB :
      M.IsBase
        (M.E \ cyclicWindow s hn σ (cyclicIndex n hn i r)) :=
    hBdual.compl_isBase_of_dual
  rw [sdiff_shifted_cyclicWindow_eq hn hrs σ i] at hB
  exact hB

end

end HigherRankKUM
