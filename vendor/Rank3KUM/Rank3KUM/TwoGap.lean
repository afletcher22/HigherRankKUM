import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Circuit

namespace Rank3KUM.TwoGap

open Set

/-!
# Universal two-gap insertion: first isolated checkpoint

This file fixes the exact Lean formulation of the frozen universal two-gap
insertion statement and proves the first two ingredients of its proof:

* nonemptiness of a symmetric-partner set, using a fundamental circuit and a
  fundamental cocircuit;
* the pure set-theoretic fact that a blocked ordered choice from two nonempty
  partner sets forces both sets to be the same singleton.

The universal two-gap theorem itself is deliberately not declared as a
theorem in this checkpoint.
-/

variable {α : Type*}

/-- The set obtained from `B` by deleting `e` and inserting `f`. -/
def exchangeSet (B : Set α) (e f : α) : Set α :=
  insert f B \ {e}

/--
An ordering of the three-element basis `D` works in the first gap `a | b`.
The four displayed bases are exactly the four new noninternal length-three
windows in

`p, a, d₀, d₁, d₂, b, c, q`.
-/
def FirstGapWorks
    (M : Matroid α) (D : Set α) (p a b c : α) : Prop :=
  ∃ d : Fin 3 ≃ D,
    M.IsBase ({p, a, (d 0 : α)} : Set α) ∧
    M.IsBase ({a, (d 0 : α), (d 1 : α)} : Set α) ∧
    M.IsBase ({(d 1 : α), (d 2 : α), b} : Set α) ∧
    M.IsBase ({(d 2 : α), b, c} : Set α)

/--
An ordering of the three-element basis `D` works in the second gap `b | c`.
The four displayed bases are exactly the four new noninternal length-three
windows in

`p, a, b, d₀, d₁, d₂, c, q`.
-/
def SecondGapWorks
    (M : Matroid α) (D : Set α) (a b c q : α) : Prop :=
  ∃ d : Fin 3 ≃ D,
    M.IsBase ({a, b, (d 0 : α)} : Set α) ∧
    M.IsBase ({b, (d 0 : α), (d 1 : α)} : Set α) ∧
    M.IsBase ({(d 1 : α), (d 2 : α), c} : Set α) ∧
    M.IsBase ({(d 2 : α), c, q} : Set α)

/-- The exact disjunctive conclusion of frozen statement `TG`. -/
def TwoGapConclusion
    (M : Matroid α) (D : Set α) (p a b c q : α) : Prop :=
  FirstGapWorks M D p a b c ∨ SecondGapWorks M D a b c q

/--
The exact frozen universal two-gap insertion proposition.

The five `List.Pairwise` and ground-difference hypotheses say precisely that
`p,a,b,c,q` are five pairwise-distinct elements of `M.E \ D`. No
looplessness, simplicity, paving, representability, connectivity, finiteness,
or density assumption is present.
-/
def UniversalTwoGapInsertion (M : Matroid α) : Prop :=
  M.eRank = 3 →
    ∀ {D : Set α} {p a b c q : α},
      M.IsBase D →
      List.Pairwise (· ≠ ·) [p, a, b, c, q] →
      p ∈ M.E \ D →
      a ∈ M.E \ D →
      b ∈ M.E \ D →
      c ∈ M.E \ D →
      q ∈ M.E \ D →
      M.IsBase ({p, a, b} : Set α) →
      M.IsBase ({a, b, c} : Set α) →
      M.IsBase ({b, c, q} : Set α) →
      TwoGapConclusion M D p a b c q

/--
The elements of `D` that are simultaneous exchange partners for `e` between
the bases `D` and `B`.
-/
def SymmetricPartners
    (M : Matroid α) (D B : Set α) (e : α) : Set α :=
  {d | d ∈ D ∧ d ∉ B ∧
    M.IsBase (exchangeSet D d e) ∧
    M.IsBase (exchangeSet B e d)}

@[simp] theorem mem_symmetricPartners
    (M : Matroid α) (D B : Set α) (e d : α) :
    d ∈ SymmetricPartners M D B e ↔
      d ∈ D ∧ d ∉ B ∧
      M.IsBase (exchangeSet D d e) ∧
      M.IsBase (exchangeSet B e d) := by
  rfl

/--
Ordinary symmetric basis exchange, packaged as nonemptiness of
`SymmetricPartners`.

The proof uses the fact that the fundamental circuit of `e` over `D` and the
fundamental cocircuit of `e` in `B` cannot meet in exactly `{e}`. A second
intersection element is a simultaneous exchange partner.
-/
theorem symmetricPartners_nonempty
    (M : Matroid α) {D B : Set α} {e : α}
    (hD : M.IsBase D) (hB : M.IsBase B)
    (heB : e ∈ B) (heD : e ∉ D) :
    (SymmetricPartners M D B e).Nonempty := by
  have heE : e ∈ M.E := hB.subset_ground heB
  have hC : M.IsCircuit (M.fundCircuit e D) :=
    hD.fundCircuit_isCircuit heE heD
  have hK : M.IsCocircuit (M.fundCocircuit e B) :=
    M.fundCocircuit_isCocircuit heB hB
  have heCK : e ∈ M.fundCircuit e D ∩ M.fundCocircuit e B :=
    ⟨M.mem_fundCircuit e D, M.mem_fundCocircuit e B⟩
  have hCK :
      (M.fundCircuit e D ∩ M.fundCocircuit e B).Nontrivial :=
    hC.isCocircuit_inter_nontrivial hK ⟨e, heCK⟩
  rcases hCK with ⟨x, hx, y, hy, hxy⟩
  have hex :
      ∃ d ∈ M.fundCircuit e D ∩ M.fundCocircuit e B, d ≠ e := by
    by_cases hxe : x = e
    · refine ⟨y, hy, ?_⟩
      intro hye
      exact hxy (hxe.trans hye.symm)
    · exact ⟨x, hx, hxe⟩
  rcases hex with ⟨d, ⟨hdC, hdK⟩, hde⟩
  have hdD : d ∈ D := by
    have hd_insert : d ∈ insert e D :=
      (M.fundCircuit_subset_insert e D) hdC
    exact (Set.mem_insert_iff.mp hd_insert).resolve_left hde
  have hdEB : d ∈ M.E \ B := by
    have hd_insert : d ∈ insert e (M.E \ B) :=
      (M.fundCocircuit_subset_insert_compl e B) hdK
    exact (Set.mem_insert_iff.mp hd_insert).resolve_left hde
  have heclD : e ∈ M.closure D := by
    rw [hD.closure_eq]
    exact heE
  have hDindep : M.Indep (insert e D \ {d}) :=
    (hD.indep.mem_fundCircuit_iff heclD heD).mp hdC
  have hDbase : M.IsBase (exchangeSet D d e) := by
    exact hD.exchange_isBase_of_indep' hdD heD hDindep
  have heFundB : e ∈ M.fundCircuit d B :=
    hB.mem_fundCocircuit_iff_mem_fundCircuit.mp hdK
  have hdclB : d ∈ M.closure B := by
    rw [hB.closure_eq]
    exact hdEB.1
  have hBindep : M.Indep (insert d B \ {e}) :=
    (hB.indep.mem_fundCircuit_iff hdclB hdEB.2).mp heFundB
  have hBbase : M.IsBase (exchangeSet B e d) := by
    exact hB.exchange_isBase_of_indep' heB hdEB.2 hBindep
  exact ⟨d, hdD, hdEB.2, hDbase, hBbase⟩

/-- A gap is blocked when its two candidate endpoint sets contain no unequal pair. -/
def GapBlocked (A B : Set α) : Prop :=
  ¬ ∃ x ∈ A, ∃ y ∈ B, x ≠ y

/--
Two nonempty candidate sets block a gap exactly when they are the same
singleton. This is the pure combinatorial reduction used twice in `TG`.
-/
theorem gapBlocked_iff_common_singleton
    {A B : Set α} (hA : A.Nonempty) (hB : B.Nonempty) :
    GapBlocked A B ↔ ∃ t, A = {t} ∧ B = {t} := by
  constructor
  · intro hblocked
    rcases hA with ⟨a, haA⟩
    rcases hB with ⟨b, hbB⟩
    have hab : a = b := by
      by_contra hab
      exact hblocked ⟨a, haA, b, hbB, hab⟩
    subst b
    refine ⟨a, ?_, ?_⟩
    · ext x
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hxA
        by_contra hxa
        exact hblocked ⟨x, hxA, a, hbB, hxa⟩
      · rintro rfl
        exact haA
    · ext y
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hyB
        by_contra hya
        exact hblocked ⟨a, haA, y, hyB, fun hay => hya hay.symm⟩
      · rintro rfl
        exact hbB
  · rintro ⟨t, rfl, rfl⟩ ⟨x, hx, y, hy, hxy⟩
    simp only [Set.mem_singleton_iff] at hx hy
    exact hxy (hx.trans hy.symm)

/--
Specialization of `gapBlocked_iff_common_singleton` to symmetric-partner
sets. Basis exchange supplies the two nonemptiness hypotheses.
-/
theorem gapBlocked_symmetricPartners_iff_common_singleton
    (M : Matroid α) {D B₁ B₂ : Set α} {e₁ e₂ : α}
    (hD : M.IsBase D)
    (hB₁ : M.IsBase B₁) (he₁B₁ : e₁ ∈ B₁) (he₁D : e₁ ∉ D)
    (hB₂ : M.IsBase B₂) (he₂B₂ : e₂ ∈ B₂) (he₂D : e₂ ∉ D) :
    GapBlocked (SymmetricPartners M D B₁ e₁)
        (SymmetricPartners M D B₂ e₂) ↔
      ∃ t,
        SymmetricPartners M D B₁ e₁ = {t} ∧
        SymmetricPartners M D B₂ e₂ = {t} := by
  exact gapBlocked_iff_common_singleton
    (symmetricPartners_nonempty M hD hB₁ he₁B₁ he₁D)
    (symmetricPartners_nonempty M hD hB₂ he₂B₂ he₂D)

end Rank3KUM.TwoGap
