import Probe.Rank4.SerialExchange
import HigherRankKUM.VHT.Theorem21
import HigherRankKUM.VHT.Covers

/-!
# KUM(4, 8) from Kotlar–Ziv

A uniformly dense rank-4 matroid on 8 elements is the disjoint union of two bases `A`, `B`
(Edmonds, via van den Heuvel–Thomassé Theorem 2.1 with `k = 2`). By Kotlar–Ziv
(`KotlarZiv.cyclic_windows_rank_four`) there are enumerations `A = {p₁, p₂, p₃, p₄}` and
`B = {q₁, q₂, q₃, q₄}` for which every cyclic 4-window of `p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄` is a basis.
This proof replaces the SAT certificate `Probe.Enc.Kum8.solves`.
-/

namespace HigherRankKUM

open Set

/-- The range of a map out of `Fin 4`, listed. -/
theorem range_fin_four {β : Type*} (g : Fin 4 → β) : Set.range g = {g 0, g 1, g 2, g 3} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

/-- A numbering `f : Fin 8 → α` of an 8-element ground set whose cyclic 4-windows are bases is a
cyclic basis ordering. -/
theorem exists_cyclicBasisOrder_of_seq {α : Type*} (N : Matroid α) (hn : 0 < 8)
    (f : Fin 8 → α) (hfE : ∀ i, f i ∈ N.E) (hsurj : ∀ e ∈ N.E, ∃ i, f i = e)
    (hEn : N.E.ncard = 8)
    (hwin : ∀ i : Fin 8, N.IsBase (Set.range fun j : Fin 4 => f (cyclicIndex 8 hn i j.val))) :
    ∃ σ : Fin 8 ≃ N.E, CyclicBasisOrder N 4 hn σ := by
  have hs : Function.Surjective (fun i : Fin 8 => (⟨f i, hfE i⟩ : N.E)) := by
    rintro ⟨e, he⟩
    obtain ⟨i, hi⟩ := hsurj e he
    exact ⟨i, Subtype.ext hi⟩
  have hb : Function.Bijective (fun i : Fin 8 => (⟨f i, hfE i⟩ : N.E)) :=
    hs.bijective_of_nat_card_le (by simp [hEn])
  exact ⟨Equiv.ofBijective _ hb, fun i => hwin i⟩

/-- **KUM(4, 8)**, from Kotlar–Ziv. -/
theorem solvesKUMAtRankSize_four_eight {α : Type*} : SolvesKUMAtRankSize α 4 8 := by
  intro N hr hn hE hRank hEcard hDense
  -- density `8/4` is density `2/1`
  have hDense2 : UniformlyDenseRatio N 2 1 := by
    intro X hX
    have h := hDense X hX
    have h2 : ((4 : ℕ) : ℕ∞) * X.encard = 4 * (((1 : ℕ) : ℕ∞) * X.encard) := by
      norm_num
    have h3 : ((8 : ℕ) : ℕ∞) * N.eRk X = 4 * (((2 : ℕ) : ℕ∞) * N.eRk X) := by
      push_cast
      ring
    rw [h2, h3] at h
    exact (ENat.mul_le_mul_left_iff (by norm_num) (by simp)).1 h
  -- Edmonds: two disjoint bases covering the ground set
  obtain ⟨P, hP, hPu⟩ := VHT.edmonds_partition VHT.theorem_2_1 N (k := 2) (n := 8) (r := 4)
    (by norm_num) hE hEcard hRank (by norm_num) hDense2
  have hZ : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have hdisj : Disjoint (P 0) (P 1) := by
    rw [Set.disjoint_left]
    intro e he0 he1
    obtain ⟨x, -, hx⟩ := hPu e ((hP 0).subset_ground he0)
    exact h01 ((hx 0 he0).trans (hx 1 he1).symm)
  have hcover : ∀ e ∈ N.E, e ∈ P 0 ∨ e ∈ P 1 := by
    intro e he
    obtain ⟨x, hx, -⟩ := hPu e he
    rcases hZ x with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  have hRank4 : N.eRank = 4 := by simpa using hRank
  -- Kotlar–Ziv
  obtain ⟨p₁, p₂, p₃, p₄, q₁, q₂, q₃, q₄, hA, hB, w0, w1, w2, w3, w4, w5, w6, w7⟩ :=
    KotlarZiv.cyclic_windows_rank_four (hP 0) (hP 1) hdisj hRank4
  have hAE : ({p₁, p₂, p₃, p₄} : Set α) ⊆ N.E := by
    rw [← hA]
    exact (hP 0).subset_ground
  have hBE : ({q₁, q₂, q₃, q₄} : Set α) ⊆ N.E := by
    rw [← hB]
    exact (hP 1).subset_ground
  have hEn : N.E.ncard = 8 := by
    have h := hE.cast_ncard_eq
    rw [hEcard] at h
    exact_mod_cast h
  refine exists_cyclicBasisOrder_of_seq N hn ![p₁, p₂, p₃, p₄, q₁, q₂, q₃, q₄] ?_ ?_ hEn ?_
  · -- the numbering stays in the ground set
    have e₁ : p₁ ∈ N.E := hAE (by simp)
    have e₂ : p₂ ∈ N.E := hAE (by simp)
    have e₃ : p₃ ∈ N.E := hAE (by simp)
    have e₄ : p₄ ∈ N.E := hAE (by simp)
    have e₅ : q₁ ∈ N.E := hBE (by simp)
    have e₆ : q₂ ∈ N.E := hBE (by simp)
    have e₇ : q₃ ∈ N.E := hBE (by simp)
    have e₈ : q₄ ∈ N.E := hBE (by simp)
    intro i
    fin_cases i
    exacts [e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈]
  · -- and covers it
    intro e he
    rcases hcover e he with h | h
    · rw [hA] at h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
    · rw [hB] at h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl | rfl | rfl
      exacts [⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩, ⟨7, rfl⟩]
  · -- the eight windows
    intro i
    fin_cases i
    · rw [range_fin_four]; exact w0
    · rw [range_fin_four]; exact w1
    · rw [range_fin_four]; exact w2
    · rw [range_fin_four]; exact w3
    · rw [range_fin_four]; exact w4
    · rw [range_fin_four]; exact w5
    · rw [range_fin_four]; exact w6
    · rw [range_fin_four]; exact w7

#print axioms solvesKUMAtRankSize_four_eight

end HigherRankKUM
