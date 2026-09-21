import Mathlib.Tactic

namespace Rank3KUM

open Finset

/--
Eight explicit cyclic orders cover every linear family of three-subsets of a
six-element set.  This is the finite combinatorial certificate used by the
`k = 2` strict case.
-/
def SixPointGoodAlternatives
    (Bad : Finset (Fin 6) → Prop) : Prop :=
  (¬ Bad ({0, 1, 2} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 3} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({3, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 1, 5} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 2, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 3} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 2} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({3, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 1, 3} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 3} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 4, 5} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 1, 4} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 3} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 3, 5} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 2} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 3} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({3, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 4} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({3, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 1, 2} : Finset (Fin 6)))

/-- The finite list of forbidden pairs defining a linear triple family on six vertices. -/
def LinearSixBad
    (Bad : Finset (Fin 6) → Prop) : Prop :=
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 1, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 1, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 1, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 2, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({1, 2, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 1, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 1, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 2, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 1, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 4, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 4, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 4, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 4, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 4, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 3, 4} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 3, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 3, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 4, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6)))

/-- The eight concrete permutations certified by `SixPointGoodAlternatives`. -/
def sixPointPerm1 : Equiv.Perm (Fin 6) :=
  Equiv.refl (Fin 6)

noncomputable def sixPointPerm2 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 2, 4, 1, 5, 3] : Fin 6 → Fin 6) (by decide)

noncomputable def sixPointPerm3 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 1, 2, 5, 4, 3] : Fin 6 → Fin 6) (by decide)

noncomputable def sixPointPerm4 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 4, 1, 3, 2, 5] : Fin 6 → Fin 6) (by decide)

noncomputable def sixPointPerm5 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 1, 5, 3, 2, 4] : Fin 6 → Fin 6) (by decide)

noncomputable def sixPointPerm6 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 3, 1, 4, 2, 5] : Fin 6 → Fin 6) (by decide)

noncomputable def sixPointPerm7 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 2, 1, 3, 5, 4] : Fin 6 → Fin 6) (by decide)

noncomputable def sixPointPerm8 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 1, 5, 3, 4, 2] : Fin 6 → Fin 6) (by decide)


/-- Cheap evaluation lemmas: avoid unfolding `Equiv.ofBijective` during `simp`. -/

@[simp] theorem sixPointPerm1_apply (i : Fin 6) : sixPointPerm1 i = i := rfl

@[simp] theorem sixPointPerm2_apply (i : Fin 6) :
    sixPointPerm2 i = (![0, 2, 4, 1, 5, 3] : Fin 6 → Fin 6) i := rfl

@[simp] theorem sixPointPerm3_apply (i : Fin 6) :
    sixPointPerm3 i = (![0, 1, 2, 5, 4, 3] : Fin 6 → Fin 6) i := rfl

@[simp] theorem sixPointPerm4_apply (i : Fin 6) :
    sixPointPerm4 i = (![0, 4, 1, 3, 2, 5] : Fin 6 → Fin 6) i := rfl

@[simp] theorem sixPointPerm5_apply (i : Fin 6) :
    sixPointPerm5 i = (![0, 1, 5, 3, 2, 4] : Fin 6 → Fin 6) i := rfl

@[simp] theorem sixPointPerm6_apply (i : Fin 6) :
    sixPointPerm6 i = (![0, 3, 1, 4, 2, 5] : Fin 6 → Fin 6) i := rfl

@[simp] theorem sixPointPerm7_apply (i : Fin 6) :
    sixPointPerm7 i = (![0, 2, 1, 3, 5, 4] : Fin 6 → Fin 6) i := rfl

@[simp] theorem sixPointPerm8_apply (i : Fin 6) :
    sixPointPerm8 i = (![0, 1, 5, 3, 4, 2] : Fin 6 → Fin 6) i := rfl

/-- The propositional core of the six-point certificate. -/
private theorem sixPointSAT
    (p012 p013 p014 p015 p023 p024 p025 p034 p035 p045 p123 p124 p125 p134 p135 p145 p234 p235 p245 p345 : Prop)
    (hlinear :
      ¬ (p012 ∧ p013) ∧
      ¬ (p012 ∧ p014) ∧
      ¬ (p012 ∧ p015) ∧
      ¬ (p012 ∧ p023) ∧
      ¬ (p012 ∧ p024) ∧
      ¬ (p012 ∧ p025) ∧
      ¬ (p012 ∧ p123) ∧
      ¬ (p012 ∧ p124) ∧
      ¬ (p012 ∧ p125) ∧
      ¬ (p013 ∧ p014) ∧
      ¬ (p013 ∧ p015) ∧
      ¬ (p013 ∧ p023) ∧
      ¬ (p013 ∧ p034) ∧
      ¬ (p013 ∧ p035) ∧
      ¬ (p013 ∧ p123) ∧
      ¬ (p013 ∧ p134) ∧
      ¬ (p013 ∧ p135) ∧
      ¬ (p014 ∧ p015) ∧
      ¬ (p014 ∧ p024) ∧
      ¬ (p014 ∧ p034) ∧
      ¬ (p014 ∧ p045) ∧
      ¬ (p014 ∧ p124) ∧
      ¬ (p014 ∧ p134) ∧
      ¬ (p014 ∧ p145) ∧
      ¬ (p015 ∧ p025) ∧
      ¬ (p015 ∧ p035) ∧
      ¬ (p015 ∧ p045) ∧
      ¬ (p015 ∧ p125) ∧
      ¬ (p015 ∧ p135) ∧
      ¬ (p015 ∧ p145) ∧
      ¬ (p023 ∧ p024) ∧
      ¬ (p023 ∧ p025) ∧
      ¬ (p023 ∧ p034) ∧
      ¬ (p023 ∧ p035) ∧
      ¬ (p023 ∧ p123) ∧
      ¬ (p023 ∧ p234) ∧
      ¬ (p023 ∧ p235) ∧
      ¬ (p024 ∧ p025) ∧
      ¬ (p024 ∧ p034) ∧
      ¬ (p024 ∧ p045) ∧
      ¬ (p024 ∧ p124) ∧
      ¬ (p024 ∧ p234) ∧
      ¬ (p024 ∧ p245) ∧
      ¬ (p025 ∧ p035) ∧
      ¬ (p025 ∧ p045) ∧
      ¬ (p025 ∧ p125) ∧
      ¬ (p025 ∧ p235) ∧
      ¬ (p025 ∧ p245) ∧
      ¬ (p034 ∧ p035) ∧
      ¬ (p034 ∧ p045) ∧
      ¬ (p034 ∧ p134) ∧
      ¬ (p034 ∧ p234) ∧
      ¬ (p034 ∧ p345) ∧
      ¬ (p035 ∧ p045) ∧
      ¬ (p035 ∧ p135) ∧
      ¬ (p035 ∧ p235) ∧
      ¬ (p035 ∧ p345) ∧
      ¬ (p045 ∧ p145) ∧
      ¬ (p045 ∧ p245) ∧
      ¬ (p045 ∧ p345) ∧
      ¬ (p123 ∧ p124) ∧
      ¬ (p123 ∧ p125) ∧
      ¬ (p123 ∧ p134) ∧
      ¬ (p123 ∧ p135) ∧
      ¬ (p123 ∧ p234) ∧
      ¬ (p123 ∧ p235) ∧
      ¬ (p124 ∧ p125) ∧
      ¬ (p124 ∧ p134) ∧
      ¬ (p124 ∧ p145) ∧
      ¬ (p124 ∧ p234) ∧
      ¬ (p124 ∧ p245) ∧
      ¬ (p125 ∧ p135) ∧
      ¬ (p125 ∧ p145) ∧
      ¬ (p125 ∧ p235) ∧
      ¬ (p125 ∧ p245) ∧
      ¬ (p134 ∧ p135) ∧
      ¬ (p134 ∧ p145) ∧
      ¬ (p134 ∧ p234) ∧
      ¬ (p134 ∧ p345) ∧
      ¬ (p135 ∧ p145) ∧
      ¬ (p135 ∧ p235) ∧
      ¬ (p135 ∧ p345) ∧
      ¬ (p145 ∧ p245) ∧
      ¬ (p145 ∧ p345) ∧
      ¬ (p234 ∧ p235) ∧
      ¬ (p234 ∧ p245) ∧
      ¬ (p234 ∧ p345) ∧
      ¬ (p235 ∧ p245) ∧
      ¬ (p235 ∧ p345) ∧
      ¬ (p245 ∧ p345)) :
    (¬ p012 ∧ ¬ p123 ∧ ¬ p234 ∧ ¬ p345 ∧ ¬ p045 ∧ ¬ p015) ∨
    (¬ p024 ∧ ¬ p124 ∧ ¬ p145 ∧ ¬ p135 ∧ ¬ p035 ∧ ¬ p023) ∨
    (¬ p012 ∧ ¬ p125 ∧ ¬ p245 ∧ ¬ p345 ∧ ¬ p034 ∧ ¬ p013) ∨
    (¬ p014 ∧ ¬ p134 ∧ ¬ p123 ∧ ¬ p235 ∧ ¬ p025 ∧ ¬ p045) ∨
    (¬ p015 ∧ ¬ p135 ∧ ¬ p235 ∧ ¬ p234 ∧ ¬ p024 ∧ ¬ p014) ∨
    (¬ p013 ∧ ¬ p134 ∧ ¬ p124 ∧ ¬ p245 ∧ ¬ p025 ∧ ¬ p035) ∨
    (¬ p012 ∧ ¬ p123 ∧ ¬ p135 ∧ ¬ p345 ∧ ¬ p045 ∧ ¬ p024) ∨
    (¬ p015 ∧ ¬ p135 ∧ ¬ p345 ∧ ¬ p234 ∧ ¬ p024 ∧ ¬ p012) := by
  classical
  obtain ⟨c012_013, c012_014, c012_015, c012_023, c012_024, c012_025, c012_123, c012_124, c012_125, c013_014, c013_015, c013_023, c013_034, c013_035, c013_123, c013_134, c013_135, c014_015, c014_024, c014_034, c014_045, c014_124, c014_134, c014_145, c015_025, c015_035, c015_045, c015_125, c015_135, c015_145, c023_024, c023_025, c023_034, c023_035, c023_123, c023_234, c023_235, c024_025, c024_034, c024_045, c024_124, c024_234, c024_245, c025_035, c025_045, c025_125, c025_235, c025_245, c034_035, c034_045, c034_134, c034_234, c034_345, c035_045, c035_135, c035_235, c035_345, c045_145, c045_245, c045_345, c123_124, c123_125, c123_134, c123_135, c123_234, c123_235, c124_125, c124_134, c124_145, c124_234, c124_245, c125_135, c125_145, c125_235, c125_245, c134_135, c134_145, c134_234, c134_345, c135_145, c135_235, c135_345, c145_245, c145_345, c234_235, c234_245, c234_345, c235_245, c235_345, c245_345⟩ := hlinear
  by_cases h012 : p012
  · -- p012 holds
    have n013 : ¬ p013 := fun hu => c012_013 ⟨h012, hu⟩
    have n014 : ¬ p014 := fun hu => c012_014 ⟨h012, hu⟩
    have n015 : ¬ p015 := fun hu => c012_015 ⟨h012, hu⟩
    have n023 : ¬ p023 := fun hu => c012_023 ⟨h012, hu⟩
    have n024 : ¬ p024 := fun hu => c012_024 ⟨h012, hu⟩
    have n025 : ¬ p025 := fun hu => c012_025 ⟨h012, hu⟩
    have n123 : ¬ p123 := fun hu => c012_123 ⟨h012, hu⟩
    have n124 : ¬ p124 := fun hu => c012_124 ⟨h012, hu⟩
    have n125 : ¬ p125 := fun hu => c012_125 ⟨h012, hu⟩
    by_cases h145 : p145
    · -- p145 holds
      have n045 : ¬ p045 := fun hu => c045_145 ⟨hu, h145⟩
      have n134 : ¬ p134 := fun hu => c134_145 ⟨hu, h145⟩
      have n135 : ¬ p135 := fun hu => c135_145 ⟨hu, h145⟩
      have n245 : ¬ p245 := fun hu => c145_245 ⟨h145, hu⟩
      have n345 : ¬ p345 := fun hu => c145_345 ⟨h145, hu⟩
      by_cases h235 : p235
      · -- p235 holds
        have n035 : ¬ p035 := fun hu => c035_235 ⟨hu, h235⟩
        have n234 : ¬ p234 := fun hu => c234_235 ⟨hu, h235⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n013, n134, n124, n245, n025, n035⟩)))))
      · -- p235 fails
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n014, n134, n123, h235, n025, n045⟩)))
    · -- p145 fails
      by_cases h035 : p035
      · -- p035 holds
        have n034 : ¬ p034 := fun hu => c034_035 ⟨hu, h035⟩
        have n045 : ¬ p045 := fun hu => c035_045 ⟨h035, hu⟩
        have n135 : ¬ p135 := fun hu => c035_135 ⟨h035, hu⟩
        have n235 : ¬ p235 := fun hu => c035_235 ⟨h035, hu⟩
        have n345 : ¬ p345 := fun hu => c035_345 ⟨h035, hu⟩
        by_cases h134 : p134
        · -- p134 holds
          have n234 : ¬ p234 := fun hu => c134_234 ⟨h134, hu⟩
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n015, n135, n235, n234, n024, n014⟩))))
        · -- p134 fails
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n014, h134, n123, n235, n025, n045⟩)))
      · -- p035 fails
        by_cases h135 : p135
        · -- p135 holds
          have n134 : ¬ p134 := fun hu => c134_135 ⟨hu, h135⟩
          have n235 : ¬ p235 := fun hu => c135_235 ⟨h135, hu⟩
          have n345 : ¬ p345 := fun hu => c135_345 ⟨h135, hu⟩
          by_cases h045 : p045
          · -- p045 holds
            have n034 : ¬ p034 := fun hu => c034_045 ⟨hu, h045⟩
            have n245 : ¬ p245 := fun hu => c045_245 ⟨h045, hu⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n013, n134, n124, n245, n025, h035⟩)))))
          · -- p045 fails
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n014, n134, n123, n235, n025, h045⟩)))
        · -- p135 fails
          exact Or.inr (Or.inl ⟨n024, n124, h145, h135, h035, n023⟩)
  · -- p012 fails
    by_cases h234 : p234
    · -- p234 holds
      have n023 : ¬ p023 := fun hu => c023_234 ⟨hu, h234⟩
      have n024 : ¬ p024 := fun hu => c024_234 ⟨hu, h234⟩
      have n034 : ¬ p034 := fun hu => c034_234 ⟨hu, h234⟩
      have n123 : ¬ p123 := fun hu => c123_234 ⟨hu, h234⟩
      have n124 : ¬ p124 := fun hu => c124_234 ⟨hu, h234⟩
      have n134 : ¬ p134 := fun hu => c134_234 ⟨hu, h234⟩
      have n235 : ¬ p235 := fun hu => c234_235 ⟨h234, hu⟩
      have n245 : ¬ p245 := fun hu => c234_245 ⟨h234, hu⟩
      have n345 : ¬ p345 := fun hu => c234_345 ⟨h234, hu⟩
      by_cases h125 : p125
      · -- p125 holds
        have n015 : ¬ p015 := fun hu => c015_125 ⟨hu, h125⟩
        have n025 : ¬ p025 := fun hu => c025_125 ⟨hu, h125⟩
        have n135 : ¬ p135 := fun hu => c125_135 ⟨h125, hu⟩
        have n145 : ¬ p145 := fun hu => c125_145 ⟨h125, hu⟩
        by_cases h035 : p035
        · -- p035 holds
          have n013 : ¬ p013 := fun hu => c013_035 ⟨hu, h035⟩
          have n045 : ¬ p045 := fun hu => c035_045 ⟨h035, hu⟩
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h012, n123, n135, n345, n045, n024⟩))))))
        · -- p035 fails
          exact Or.inr (Or.inl ⟨n024, n124, n145, n135, h035, n023⟩)
      · -- p125 fails
        by_cases h013 : p013
        · -- p013 holds
          have n014 : ¬ p014 := fun hu => c013_014 ⟨h013, hu⟩
          have n015 : ¬ p015 := fun hu => c013_015 ⟨h013, hu⟩
          have n035 : ¬ p035 := fun hu => c013_035 ⟨h013, hu⟩
          have n135 : ¬ p135 := fun hu => c013_135 ⟨h013, hu⟩
          by_cases h145 : p145
          · -- p145 holds
            have n045 : ¬ p045 := fun hu => c045_145 ⟨hu, h145⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h012, n123, n135, n345, n045, n024⟩))))))
          · -- p145 fails
            exact Or.inr (Or.inl ⟨n024, n124, h145, n135, n035, n023⟩)
        · -- p013 fails
          exact Or.inr (Or.inr (Or.inl ⟨h012, h125, n245, n345, n034, h013⟩))
    · -- p234 fails
      by_cases h045 : p045
      · -- p045 holds
        have n014 : ¬ p014 := fun hu => c014_045 ⟨hu, h045⟩
        have n015 : ¬ p015 := fun hu => c015_045 ⟨hu, h045⟩
        have n024 : ¬ p024 := fun hu => c024_045 ⟨hu, h045⟩
        have n025 : ¬ p025 := fun hu => c025_045 ⟨hu, h045⟩
        have n034 : ¬ p034 := fun hu => c034_045 ⟨hu, h045⟩
        have n035 : ¬ p035 := fun hu => c035_045 ⟨hu, h045⟩
        have n145 : ¬ p145 := fun hu => c045_145 ⟨h045, hu⟩
        have n245 : ¬ p245 := fun hu => c045_245 ⟨h045, hu⟩
        have n345 : ¬ p345 := fun hu => c045_345 ⟨h045, hu⟩
        by_cases h135 : p135
        · -- p135 holds
          have n013 : ¬ p013 := fun hu => c013_135 ⟨hu, h135⟩
          have n123 : ¬ p123 := fun hu => c123_135 ⟨hu, h135⟩
          have n125 : ¬ p125 := fun hu => c125_135 ⟨hu, h135⟩
          have n134 : ¬ p134 := fun hu => c134_135 ⟨hu, h135⟩
          have n235 : ¬ p235 := fun hu => c135_235 ⟨h135, hu⟩
          exact Or.inr (Or.inr (Or.inl ⟨h012, n125, n245, n345, n034, n013⟩))
        · -- p135 fails
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨n015, h135, n345, h234, n024, h012⟩)))))))
      · -- p045 fails
        by_cases h123 : p123
        · -- p123 holds
          have n013 : ¬ p013 := fun hu => c013_123 ⟨hu, h123⟩
          have n023 : ¬ p023 := fun hu => c023_123 ⟨hu, h123⟩
          have n124 : ¬ p124 := fun hu => c123_124 ⟨h123, hu⟩
          have n125 : ¬ p125 := fun hu => c123_125 ⟨h123, hu⟩
          have n134 : ¬ p134 := fun hu => c123_134 ⟨h123, hu⟩
          have n135 : ¬ p135 := fun hu => c123_135 ⟨h123, hu⟩
          have n235 : ¬ p235 := fun hu => c123_235 ⟨h123, hu⟩
          by_cases h024 : p024
          · -- p024 holds
            have n014 : ¬ p014 := fun hu => c014_024 ⟨hu, h024⟩
            have n025 : ¬ p025 := fun hu => c024_025 ⟨h024, hu⟩
            have n034 : ¬ p034 := fun hu => c024_034 ⟨h024, hu⟩
            have n245 : ¬ p245 := fun hu => c024_245 ⟨h024, hu⟩
            by_cases h345 : p345
            · -- p345 holds
              have n035 : ¬ p035 := fun hu => c035_345 ⟨hu, h345⟩
              have n145 : ¬ p145 := fun hu => c145_345 ⟨hu, h345⟩
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n013, n134, n124, n245, n025, n035⟩)))))
            · -- p345 fails
              exact Or.inr (Or.inr (Or.inl ⟨h012, n125, n245, h345, n034, n013⟩))
          · -- p024 fails
            by_cases h145 : p145
            · -- p145 holds
              have n014 : ¬ p014 := fun hu => c014_145 ⟨hu, h145⟩
              have n015 : ¬ p015 := fun hu => c015_145 ⟨hu, h145⟩
              have n245 : ¬ p245 := fun hu => c145_245 ⟨h145, hu⟩
              have n345 : ¬ p345 := fun hu => c145_345 ⟨h145, hu⟩
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n015, n135, n235, h234, h024, n014⟩))))
            · -- p145 fails
              by_cases h035 : p035
              · -- p035 holds
                have n015 : ¬ p015 := fun hu => c015_035 ⟨hu, h035⟩
                have n025 : ¬ p025 := fun hu => c025_035 ⟨hu, h035⟩
                have n034 : ¬ p034 := fun hu => c034_035 ⟨hu, h035⟩
                have n345 : ¬ p345 := fun hu => c035_345 ⟨h035, hu⟩
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨n015, n135, n345, h234, h024, h012⟩)))))))
              · -- p035 fails
                exact Or.inr (Or.inl ⟨h024, n124, h145, n135, h035, n023⟩)
        · -- p123 fails
          by_cases h345 : p345
          · -- p345 holds
            have n034 : ¬ p034 := fun hu => c034_345 ⟨hu, h345⟩
            have n035 : ¬ p035 := fun hu => c035_345 ⟨hu, h345⟩
            have n134 : ¬ p134 := fun hu => c134_345 ⟨hu, h345⟩
            have n135 : ¬ p135 := fun hu => c135_345 ⟨hu, h345⟩
            have n145 : ¬ p145 := fun hu => c145_345 ⟨hu, h345⟩
            have n235 : ¬ p235 := fun hu => c235_345 ⟨hu, h345⟩
            have n245 : ¬ p245 := fun hu => c245_345 ⟨hu, h345⟩
            by_cases h014 : p014
            · -- p014 holds
              have n013 : ¬ p013 := fun hu => c013_014 ⟨hu, h014⟩
              have n015 : ¬ p015 := fun hu => c014_015 ⟨h014, hu⟩
              have n024 : ¬ p024 := fun hu => c014_024 ⟨h014, hu⟩
              have n124 : ¬ p124 := fun hu => c014_124 ⟨h014, hu⟩
              by_cases h023 : p023
              · -- p023 holds
                have n025 : ¬ p025 := fun hu => c023_025 ⟨h023, hu⟩
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n013, n134, n124, n245, n025, n035⟩)))))
              · -- p023 fails
                exact Or.inr (Or.inl ⟨n024, n124, n145, n135, n035, h023⟩)
            · -- p014 fails
              by_cases h025 : p025
              · -- p025 holds
                have n015 : ¬ p015 := fun hu => c015_025 ⟨hu, h025⟩
                have n023 : ¬ p023 := fun hu => c023_025 ⟨hu, h025⟩
                have n024 : ¬ p024 := fun hu => c024_025 ⟨hu, h025⟩
                have n125 : ¬ p125 := fun hu => c025_125 ⟨h025, hu⟩
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n015, n135, n235, h234, n024, h014⟩))))
              · -- p025 fails
                exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h014, n134, h123, n235, h025, h045⟩)))
          · -- p345 fails
            by_cases h015 : p015
            · -- p015 holds
              have n013 : ¬ p013 := fun hu => c013_015 ⟨hu, h015⟩
              have n014 : ¬ p014 := fun hu => c014_015 ⟨hu, h015⟩
              have n025 : ¬ p025 := fun hu => c015_025 ⟨h015, hu⟩
              have n035 : ¬ p035 := fun hu => c015_035 ⟨h015, hu⟩
              have n125 : ¬ p125 := fun hu => c015_125 ⟨h015, hu⟩
              have n135 : ¬ p135 := fun hu => c015_135 ⟨h015, hu⟩
              have n145 : ¬ p145 := fun hu => c015_145 ⟨h015, hu⟩
              by_cases h024 : p024
              · -- p024 holds
                have n023 : ¬ p023 := fun hu => c023_024 ⟨hu, h024⟩
                have n034 : ¬ p034 := fun hu => c024_034 ⟨h024, hu⟩
                have n124 : ¬ p124 := fun hu => c024_124 ⟨h024, hu⟩
                have n245 : ¬ p245 := fun hu => c024_245 ⟨h024, hu⟩
                exact Or.inr (Or.inr (Or.inl ⟨h012, n125, n245, h345, n034, n013⟩))
              · -- p024 fails
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h012, h123, n135, h345, h045, h024⟩))))))
            · -- p015 fails
              exact Or.inl ⟨h012, h123, h234, h345, h045, h015⟩

/--
A family satisfying the explicit linearity certificate obeys one of the
eight certified cyclic-order alternatives.
-/
theorem sixPointGoodAlternatives_of_linear
    (Bad : Finset (Fin 6) → Prop)
    (hlinear : LinearSixBad Bad) :
    SixPointGoodAlternatives Bad := by
  unfold LinearSixBad at hlinear
  unfold SixPointGoodAlternatives
  exact
    sixPointSAT
      (Bad ({0, 1, 2} : Finset (Fin 6)))
      (Bad ({0, 1, 3} : Finset (Fin 6)))
      (Bad ({0, 1, 4} : Finset (Fin 6)))
      (Bad ({0, 1, 5} : Finset (Fin 6)))
      (Bad ({0, 2, 3} : Finset (Fin 6)))
      (Bad ({0, 2, 4} : Finset (Fin 6)))
      (Bad ({0, 2, 5} : Finset (Fin 6)))
      (Bad ({0, 3, 4} : Finset (Fin 6)))
      (Bad ({0, 3, 5} : Finset (Fin 6)))
      (Bad ({0, 4, 5} : Finset (Fin 6)))
      (Bad ({1, 2, 3} : Finset (Fin 6)))
      (Bad ({1, 2, 4} : Finset (Fin 6)))
      (Bad ({1, 2, 5} : Finset (Fin 6)))
      (Bad ({1, 3, 4} : Finset (Fin 6)))
      (Bad ({1, 3, 5} : Finset (Fin 6)))
      (Bad ({1, 4, 5} : Finset (Fin 6)))
      (Bad ({2, 3, 4} : Finset (Fin 6)))
      (Bad ({2, 3, 5} : Finset (Fin 6)))
      (Bad ({2, 4, 5} : Finset (Fin 6)))
      (Bad ({3, 4, 5} : Finset (Fin 6)))
      hlinear

#print axioms Rank3KUM.sixPointGoodAlternatives_of_linear

end Rank3KUM
