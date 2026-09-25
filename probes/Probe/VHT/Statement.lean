import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# van den Heuvel–Thomassé, Theorem 2.1: statement and basic counting

J. van den Heuvel and S. Thomassé, *Cyclic orderings and cyclic arboricity of matroids*
(arXiv:0912.2929), Theorem 2.1.

The points of the `D`-gon are `ZMod D`. A mapping `φ` places element `e` on the arc
`φ e, φ e + 1, …, φ e + ω e - 1`, so the point `x` is covered by `e` exactly when
`(x - φ e).val < ω e`.

Theorem 2.1 says that the sets of elements covering each point can all be made independent if and
only if every finite `A ⊆ E` has total weight at most `D · r(A)`. Only the direction
(b) ⇒ (a) is used, and `Statement α` records it as a proposition, so that its consequences
(coprime KUM, Edmonds' covering, double covers) can be developed before its proof.
-/

namespace HigherRankKUM.VHT

open Set

variable {α : Type*}

/-- The ground-set elements whose arc covers the point `x`. -/
def arcSet (M : Matroid α) {D : ℕ} (φ : α → ZMod D) (ω : α → ℕ) (x : ZMod D) : Set α :=
  {e | e ∈ M.E ∧ (x - φ e).val < ω e}

theorem arcSet_subset (M : Matroid α) {D : ℕ} (φ : α → ZMod D) (ω : α → ℕ) (x : ZMod D) :
    arcSet M φ ω x ⊆ M.E := fun _ h => h.1

/-- Condition (b) of Theorem 2.1: every finite subset `A` of the ground set has total weight at
most `D · r(A)`. -/
def WeightBounded (M : Matroid α) (ω : α → ℕ) (D : ℕ) : Prop :=
  ∀ A : Finset α, (A : Set α) ⊆ M.E → ((A.sum ω : ℕ) : ℕ∞) ≤ (D : ℕ∞) * M.eRk (A : Set α)

/-- Theorem 2.1 of van den Heuvel–Thomassé, direction (b) ⇒ (a), for all matroids on `α`. -/
def Statement (α : Type*) : Prop :=
  ∀ (M : Matroid α) (ω : α → ℕ) (D : ℕ), 0 < D → M.E.Finite → M.Loopless →
    WeightBounded M ω D → ∃ φ : α → ZMod D, ∀ x : ZMod D, M.Indep (arcSet M φ ω x)

/-- On the `D`-gon, exactly `min w D` points lie on an arc of length `w`. -/
theorem card_arc {D : ℕ} [NeZero D] (y : ZMod D) (w : ℕ) :
    (Finset.univ.filter fun x : ZMod D => (x - y).val < w).card = min w D := by
  have h1 : (Finset.univ.filter fun x : ZMod D => (x - y).val < w).card =
      (Finset.univ.filter fun z : ZMod D => z.val < w).card := by
    apply Finset.card_bij (fun x _ => x - y)
    · intro x hx
      simpa using hx
    · intro a _ b _ h
      simpa using h
    · intro z hz
      exact ⟨z + y, by simpa using hz, by ring⟩
  have h2 : (Finset.univ.filter fun z : ZMod D => z.val < w).card =
      ((Finset.range D).filter fun n => n < w).card := by
    apply Finset.card_bij (fun z _ => z.val)
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp [ZMod.val_lt, hz]
    · intro a _ b _ h
      exact ZMod.val_injective D h
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      refine ⟨(n : ZMod D), ?_, ?_⟩
      · simp [ZMod.val_natCast, Nat.mod_eq_of_lt hn.1, hn.2]
      · simp [ZMod.val_natCast, Nat.mod_eq_of_lt hn.1]
  have h3 : (Finset.range D).filter (fun n => n < w) = Finset.range (min w D) := by
    ext n
    simp [Finset.mem_filter, Finset.mem_range, lt_min_iff, and_comm]
  rw [h1, h2, h3, Finset.card_range]

end HigherRankKUM.VHT
