import Probe.Chain10
import Probe.EncFBridge
import HigherRankKUM.VHT.Covers
import HigherRankKUM.VHT.Theorem21

/-!
# Rank-4 KUM on 10 elements from a pair chain

Van den Heuvel–Thomassé with weight 2 on `ZMod 5` (`VHT.double_cover`) maps a uniformly dense
rank-4 matroid on 10 elements to `ZMod 5` so that every arc `φ⁻¹(x) ∪ φ⁻¹(x - 1)` is a basis.
The fibre sizes `f x` satisfy `f x + f (x - 1) = 4` around a cycle of odd length, so every fibre
has 2 elements. Numbering fibre `i` at positions `2i` and `2i + 1` makes the five sets
`P_i ∪ P_{i+1}` (`P_i = {2i, 2i+1}`) bases: a chain of five pairs.

The certificate `Chain10.no_model` shows that a rank-4 matroid on 10 elements with such a chain
has a cyclic basis ordering: an orientation of the chain, or of a chain obtained by re-splitting
one window `P_x ∪ P_{x+1}`. No case analysis on tight sets, dangerous planes or heavy flats is
needed.
-/

namespace HigherRankKUM

open Set Probe.Enc
open scoped Matroid

variable {α : Type*}

set_option maxRecDepth 100000

/-- A numbering of a rank-4 matroid on 10 elements whose five chain sets are bases gives a cyclic
basis ordering. -/
theorem cbo_of_chain10 {M : Matroid α} (hRank : M.eRank = 4) (pos : Fin 10 ≃ M.E)
    (hchain : ∀ X v, (X, v, true) ∈ Chain10.chainFacts10 → v ≤ maskRank M pos X) :
    ∃ τ : Fin 10 ≃ M.E, CyclicBasisOrder M 4 (by norm_num) τ := by
  by_contra hno
  exact Chain10.no_model (rankModelF_of_pos hRank (by norm_num) pos (fun X _ => by simp) hchain
    (fun X v h => by simp [Chain10.chainFacts10] at h) hno)

/-- The fibre of `φ` over `x`. -/
def fibre5 (M : Matroid α) (φ : α → ZMod 5) (x : ZMod 5) : Set α := {e | e ∈ M.E ∧ φ e = x}

theorem arcSet_two_eq (M : Matroid α) (φ : α → ZMod 5) (x : ZMod 5) :
    VHT.arcSet M φ (fun _ => 2) x = fibre5 M φ x ∪ fibre5 M φ (x - 1) := by
  have key : ∀ y z : ZMod 5, (z - y).val < 2 ↔ (y = z ∨ y = z - 1) := by decide
  ext e
  simp only [VHT.arcSet, fibre5, mem_setOf_eq, mem_union, key]
  tauto

/-- Every fibre of a weight-2 cover of a rank-4 matroid by the arcs over `ZMod 5` has 2
elements. -/
theorem fibre5_ncard {M : Matroid α} (hE : M.E.Finite) (hRank : M.eRank = 4) {φ : α → ZMod 5}
    (hφ : ∀ x, M.IsBase (VHT.arcSet M φ (fun _ => 2) x)) (x : ZMod 5) :
    (fibre5 M φ x).ncard = 2 := by
  have hfin : ∀ y, (fibre5 M φ y).Finite := fun y => hE.subset fun e he => he.1
  have hsum : ∀ y : ZMod 5, (fibre5 M φ y).ncard + (fibre5 M φ (y - 1)).ncard = 4 := by
    intro y
    have hdisj : Disjoint (fibre5 M φ y) (fibre5 M φ (y - 1)) := by
      rw [Set.disjoint_left]
      rintro e ⟨-, h1⟩ ⟨-, h2⟩
      have hne : ∀ z : ZMod 5, z ≠ z - 1 := by decide
      exact hne y (h1.symm.trans h2)
    have hfinA : (VHT.arcSet M φ (fun _ => 2) y).Finite :=
      hE.subset (VHT.arcSet_subset M φ _ y)
    have h4 : (VHT.arcSet M φ (fun _ => 2) y).ncard = 4 := by
      have h := (hφ y).encard_eq_eRank
      rw [hRank, ← hfinA.cast_ncard_eq] at h
      exact_mod_cast h
    rw [arcSet_two_eq, Set.ncard_union_eq hdisj (hfin y) (hfin (y - 1))] at h4
    exact h4
  have h0 := hsum 0
  have h1 := hsum 1
  have h2 := hsum 2
  have h3 := hsum 3
  have h4 := hsum 4
  have e0 : (0 : ZMod 5) - 1 = 4 := by decide
  have e1 : (1 : ZMod 5) - 1 = 0 := by decide
  have e2 : (2 : ZMod 5) - 1 = 1 := by decide
  have e3 : (3 : ZMod 5) - 1 = 2 := by decide
  have e4 : (4 : ZMod 5) - 1 = 3 := by decide
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  have hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
    revert x
    decide
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega

/-- A numbering of the ground set that puts fibre `i` at positions `2i` and `2i + 1`. -/
theorem exists_pos_of_fibres {M : Matroid α} (hE : M.E.Finite)
    (hEcard : M.E.encard = ((10 : ℕ) : ℕ∞)) (hRank : M.eRank = 4) {φ : α → ZMod 5}
    (hφ : ∀ x, M.IsBase (VHT.arcSet M φ (fun _ => 2) x)) :
    ∃ pos : Fin 10 ≃ M.E, ∀ p : Fin 10, φ (pos p) = (((p : ℕ) / 2 : ℕ) : ZMod 5) := by
  have hcard : ∀ i : Fin 5, (fibre5 M φ ((i : ℕ) : ZMod 5)).encard = ((2 : ℕ) : ℕ∞) := by
    intro i
    have hfin : (fibre5 M φ ((i : ℕ) : ZMod 5)).Finite := hE.subset fun e he => he.1
    rw [← hfin.cast_ncard_eq, fibre5_ncard hE hRank hφ]
  let g : ∀ i : Fin 5, Fin 2 ≃ fibre5 M φ ((i : ℕ) : ZMod 5) := fun i =>
    finEquivOfSetEncard (hE.subset fun e he => he.1) (hcard i)
  let G : Fin 10 → M.E := fun p =>
    ⟨(g ⟨(p : ℕ) / 2, by have := p.isLt; omega⟩ ⟨(p : ℕ) % 2, by omega⟩ : α),
      (g ⟨(p : ℕ) / 2, by have := p.isLt; omega⟩ ⟨(p : ℕ) % 2, by omega⟩).2.1⟩
  have hG : ∀ p, φ (G p) = (((p : ℕ) / 2 : ℕ) : ZMod 5) := fun p =>
    (g ⟨(p : ℕ) / 2, by have := p.isLt; omega⟩ ⟨(p : ℕ) % 2, by omega⟩).2.2
  have hdiv : ∀ p q : Fin 10, (((p : ℕ) / 2 : ℕ) : ZMod 5) = (((q : ℕ) / 2 : ℕ) : ZMod 5) →
      (p : ℕ) / 2 = (q : ℕ) / 2 := by decide
  have hkey : ∀ (i j : Fin 5) (b c : Fin 2), i = j → ((g i b : α) = (g j c : α)) → b = c := by
    rintro i j b c rfl h
    exact (g i).injective (Subtype.ext h)
  have hinj : Function.Injective G := by
    intro p q hpq
    have hφpq : (((p : ℕ) / 2 : ℕ) : ZMod 5) = (((q : ℕ) / 2 : ℕ) : ZMod 5) := by
      rw [← hG p, ← hG q, hpq]
    have hd := hdiv p q hφpq
    have hm := hkey ⟨(p : ℕ) / 2, by have := p.isLt; omega⟩
      ⟨(q : ℕ) / 2, by have := q.isLt; omega⟩ ⟨(p : ℕ) % 2, by omega⟩ ⟨(q : ℕ) % 2, by omega⟩
      (Fin.ext hd) (congrArg Subtype.val hpq)
    have hm' : (p : ℕ) % 2 = (q : ℕ) % 2 := congrArg Fin.val hm
    exact Fin.ext (by omega)
  let e0 : Fin 10 ≃ M.E := finEquivGround hE hEcard
  have hsurj : Function.Surjective G := by
    have hs : Function.Surjective (e0.symm ∘ G) :=
      Finite.injective_iff_surjective.1 (e0.symm.injective.comp hinj)
    intro y
    obtain ⟨p, hp⟩ := hs (e0.symm y)
    exact ⟨p, e0.symm.injective hp⟩
  exact ⟨Equiv.ofBijective G ⟨hinj, hsurj⟩, fun p => hG p⟩

/-- With fibre `i` at positions `2i`, `2i + 1`, the five chain sets contain arcs, so they are
bases. -/
theorem chain_facts {M : Matroid α} (hRank : M.eRank = 4) {φ : α → ZMod 5}
    (hφ : ∀ x, M.IsBase (VHT.arcSet M φ (fun _ => 2) x)) (pos : Fin 10 ≃ M.E)
    (hpos : ∀ p : Fin 10, φ (pos p) = (((p : ℕ) / 2 : ℕ) : ZMod 5)) :
    ∀ X v, (X, v, true) ∈ Chain10.chainFacts10 → v ≤ maskRank M pos X := by
  have key : ∀ (x : ZMod 5) (X : ℕ),
      (∀ p : Fin 10, (x - (((p : ℕ) / 2 : ℕ) : ZMod 5)).val < 2 → X.testBit p = true) →
      4 ≤ maskRank M pos X := by
    intro x X hX
    refine four_le_maskRank hRank pos ?_ (hφ x)
    rintro e ⟨he, hlt⟩
    obtain ⟨p, hp⟩ := pos.surjective ⟨e, he⟩
    have hφe : φ e = (((p : ℕ) / 2 : ℕ) : ZMod 5) := by
      rw [← hpos p, hp]
    refine ⟨p, hX p ?_, by rw [hp]⟩
    rw [← hφe]
    exact hlt
  intro X v h
  have hcases : (X = 15 ∧ v = 4) ∨ (X = 60 ∧ v = 4) ∨ (X = 240 ∧ v = 4) ∨ (X = 960 ∧ v = 4) ∨
      (X = 771 ∧ v = 4) := by
    simp [Chain10.chainFacts10] at h
    tauto
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key 1 15 (by decide)
  · exact key 2 60 (by decide)
  · exact key 3 240 (by decide)
  · exact key 4 960 (by decide)
  · exact key 0 771 (by decide)

/-- **Rank-4 KUM on 10 elements**: a van den Heuvel–Thomassé pair chain and one certificate. -/
theorem solvesKUMAtRankSize_four_ten_of_pairChain : SolvesKUMAtRankSize α 4 10 := by
  intro M hr hn hE hRank hEcard hDense
  have hRank4 : M.eRank = 4 := by simpa using hRank
  obtain ⟨φ, hφ⟩ := VHT.double_cover VHT.theorem_2_1 M (k := 2) (by norm_num) hE
    (hEcard.trans (by norm_num)) hRank (by simpa using hDense)
  obtain ⟨pos, hpos⟩ := exists_pos_of_fibres hE hEcard hRank4 hφ
  exact cbo_of_chain10 hRank4 pos (chain_facts hRank4 hφ pos hpos)

#print axioms solvesKUMAtRankSize_four_ten_of_pairChain

end HigherRankKUM
