import Mathlib.Logic.Relation
import Mathlib.Tactic

namespace HigherRankKUM
namespace PotentialAscent

/-- A bounded natural-valued potential turns local strict ascent into global
termination at a good state.

This is deliberately independent of matroids.  In the rank-four repair
application, `move x y` will mean that `y` is obtained from `x` by one legal
admissibility-preserving full `2+2` repartition, `good` will mean orientable,
and `potential` will be a closure-incidence score.

The theorem isolates the easy termination part of that strategy: the hard
matroid-specific obligation is exactly to prove that every non-good state has
some legal move with strictly larger bounded potential. -/
theorem exists_reachable_good_of_bounded_strict_ascent
    {σ : Type*}
    (move : σ → σ → Prop)
    (good : σ → Prop)
    (potential : σ → ℕ)
    (bound : ℕ)
    (hbound : ∀ x, potential x ≤ bound)
    (hascent : ∀ x, ¬ good x → ∃ y, move x y ∧ potential x < potential y) :
    ∀ x, ∃ y, Relation.ReflTransGen move x y ∧ good y := by
  have haux : ∀ n : ℕ, ∀ x : σ, bound - potential x = n →
      ∃ y, Relation.ReflTransGen move x y ∧ good y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hx
        by_cases hxgood : good x
        · exact ⟨x, Relation.ReflTransGen.refl, hxgood⟩
        · obtain ⟨y, hmove, hinc⟩ := hascent x hxgood
          have hybound : potential y ≤ bound := hbound y
          have hdec : bound - potential y < bound - potential x := by
            omega
          have hdec' : bound - potential y < n := by
            simpa [hx] using hdec
          obtain ⟨z, hyz, hzgood⟩ :=
            ih (bound - potential y) hdec' y rfl
          exact ⟨z, Relation.ReflTransGen.head hmove hyz, hzgood⟩
  intro x
  exact haux (bound - potential x) x rfl

/-- Contrapositive local form: if a state has no strictly potential-increasing
legal move, then the ascent hypothesis already forces it to be good. -/
theorem good_of_no_strict_ascent
    {σ : Type*}
    (move : σ → σ → Prop)
    (good : σ → Prop)
    (potential : σ → ℕ)
    (hascent : ∀ x, ¬ good x → ∃ y, move x y ∧ potential x < potential y)
    (x : σ)
    (hmax : ∀ y, move x y → potential y ≤ potential x) :
    good x := by
  by_contra hx
  obtain ⟨y, hmove, hinc⟩ := hascent x hx
  exact (not_lt_of_ge (hmax y hmove)) hinc

/-- A weaker and more robust termination principle: a non-good state may
terminate immediately by moving directly to a good state, or else it must
strictly increase the bounded natural-valued potential.

This is useful when the potential has plateaus that nevertheless contain an
edge directly into the good region.  Only the genuine continuation branch
needs strict ascent. -/
theorem exists_reachable_good_of_bounded_escape_or_strict_ascent
    {σ : Type*}
    (move : σ → σ → Prop)
    (good : σ → Prop)
    (potential : σ → ℕ)
    (bound : ℕ)
    (hbound : ∀ x, potential x ≤ bound)
    (hstep : ∀ x, ¬ good x →
      (∃ y, move x y ∧ good y) ∨
      (∃ y, move x y ∧ potential x < potential y)) :
    ∀ x, ∃ y, Relation.ReflTransGen move x y ∧ good y := by
  have haux : ∀ n : ℕ, ∀ x : σ, bound - potential x = n →
      ∃ y, Relation.ReflTransGen move x y ∧ good y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hx
        by_cases hxgood : good x
        · exact ⟨x, Relation.ReflTransGen.refl, hxgood⟩
        · rcases hstep x hxgood with hescape | hascent
          · obtain ⟨y, hmove, hygood⟩ := hescape
            exact ⟨y,
              Relation.ReflTransGen.head hmove Relation.ReflTransGen.refl,
              hygood⟩
          · obtain ⟨y, hmove, hinc⟩ := hascent
            have hybound : potential y ≤ bound := hbound y
            have hdec : bound - potential y < bound - potential x := by
              omega
            have hdec' : bound - potential y < n := by
              simpa [hx] using hdec
            obtain ⟨z, hyz, hzgood⟩ :=
              ih (bound - potential y) hdec' y rfl
            exact ⟨z, Relation.ReflTransGen.head hmove hyz, hzgood⟩
  intro x
  exact haux (bound - potential x) x rfl

/-- Local-maximum form of the escape-or-ascent principle.  If strict ascent is
unavailable at `x`, the step hypothesis says that `x` is already good or has
a one-step escape directly to a good state. -/
theorem good_or_exists_good_move_of_no_strict_ascent
    {σ : Type*}
    (move : σ → σ → Prop)
    (good : σ → Prop)
    (potential : σ → ℕ)
    (hstep : ∀ x, ¬ good x →
      (∃ y, move x y ∧ good y) ∨
      (∃ y, move x y ∧ potential x < potential y))
    (x : σ)
    (hmax : ∀ y, move x y → potential y ≤ potential x) :
    good x ∨ ∃ y, move x y ∧ good y := by
  by_cases hx : good x
  · exact Or.inl hx
  · right
    rcases hstep x hx with hescape | hascent
    · exact hescape
    · obtain ⟨y, hmove, hinc⟩ := hascent
      exact ((not_lt_of_ge (hmax y hmove)) hinc).elim

end PotentialAscent
end HigherRankKUM
