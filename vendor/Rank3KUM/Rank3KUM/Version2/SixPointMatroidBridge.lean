import Rank3KUM.Version2.SixPointLemma9
import Rank3KUM.SixPointMatroid

namespace Rank3KUM.Version2

open Finset Set

noncomputable section

variable {α : Type*}

/-- The actual bad three-subsets of a fixed six-point enumeration. -/
def badTripleFamily6
    (M : Matroid α) (enum : Fin 6 ≃ M.E) :
    Finset (Finset (Fin 6)) := by
  classical
  exact allTriples6.filter fun T => SixPointBad M enum T

@[simp] theorem mem_badTripleFamily6_iff
    (M : Matroid α) (enum : Fin 6 ≃ M.E)
    (T : Finset (Fin 6)) :
    T ∈ badTripleFamily6 M enum ↔
      T.card = 3 ∧ SixPointBad M enum T := by
  classical
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_powersetCard.mp h'.1).2, h'.2⟩
  · rintro ⟨hcard, hbad⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hbad⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hcard⟩

/--
Two distinct triples meeting in at least two points can be written with a
common pair and distinct residual vertices.
-/
theorem exists_shared_pair_residuals_of_three_sets
    {β : Type*} [DecidableEq β]
    {A B : Finset β}
    (hAcard : A.card = 3)
    (hBcard : B.card = 3)
    (hAB : A ≠ B)
    (hinter : 2 ≤ (A ∩ B).card) :
    ∃ i j c d : β,
      i ≠ j ∧ i ≠ c ∧ i ≠ d ∧
      j ≠ c ∧ j ≠ d ∧ c ≠ d ∧
      A = {i, j, c} ∧ B = {i, j, d} := by
  have hnontrivial : (A ∩ B).Nontrivial :=
    Finset.one_lt_card_iff_nontrivial.mp (by omega)
  rw [Finset.Nontrivial] at hnontrivial
  obtain ⟨i, hi, j, hj, hij⟩ := hnontrivial
  have hiA : i ∈ A := (Finset.mem_inter.mp hi).1
  have hiB : i ∈ B := (Finset.mem_inter.mp hi).2
  have hjA : j ∈ A := (Finset.mem_inter.mp hj).1
  have hjB : j ∈ B := (Finset.mem_inter.mp hj).2
  let P : Finset β := {i, j}
  have hPcard : P.card = 2 := by
    simp [P, hij]
  have hPA : P ⊆ A := by
    intro x hx
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hiA
    · exact hjA
  have hPB : P ⊆ B := by
    intro x hx
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hiB
    · exact hjB
  have hAdiffCard : (A \ P).card = 1 := by
    rw [Finset.card_sdiff_of_subset hPA, hAcard, hPcard]
  have hBdiffCard : (B \ P).card = 1 := by
    rw [Finset.card_sdiff_of_subset hPB, hBcard, hPcard]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hAdiffCard
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hBdiffCard
  have hcDiff : c ∈ A \ P := by rw [hc]; simp
  have hdDiff : d ∈ B \ P := by rw [hd]; simp
  have hcP : c ∉ P := (Finset.mem_sdiff.mp hcDiff).2
  have hdP : d ∉ P := (Finset.mem_sdiff.mp hdDiff).2
  have hic : i ≠ c := by
    intro h
    apply hcP
    rw [← h]
    simp [P]
  have hjc : j ≠ c := by
    intro h
    apply hcP
    rw [← h]
    simp [P]
  have hid : i ≠ d := by
    intro h
    apply hdP
    rw [← h]
    simp [P]
  have hjd : j ≠ d := by
    intro h
    apply hdP
    rw [← h]
    simp [P]
  have hAeq : A = {i, j, c} := by
    have hU := Finset.sdiff_union_of_subset hPA
    rw [hc] at hU
    rw [← hU]
    ext x
    simp only [P, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_insert]
    tauto
  have hBeq : B = {i, j, d} := by
    have hU := Finset.sdiff_union_of_subset hPB
    rw [hd] at hU
    rw [← hU]
    ext x
    simp only [P, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_insert]
    tauto
  have hcd : c ≠ d := by
    intro h
    apply hAB
    rw [hAeq, hBeq, h]
  exact ⟨i, j, c, d, hij, hic, hid, hjc, hjd, hcd, hAeq, hBeq⟩

/-- In the strict `k = 2` matroid case, the actual bad triples form a linear family. -/
theorem badTripleFamily6_linear_of_strict_two
    (M : Matroid α)
    (hLoopless : M.Loopless)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hStrict : StrictlyUniformlyDense M 2)
    (enum : Fin 6 ≃ M.E) :
    LinearTripleFamily6 (badTripleFamily6 M enum) := by
  classical
  constructor
  · intro T hT
    exact ((mem_badTripleFamily6_iff M enum T).mp hT).1
  · intro A hAF B hBF hAB
    have hA := (mem_badTripleFamily6_iff M enum A).mp hAF
    have hB := (mem_badTripleFamily6_iff M enum B).mp hBF
    by_contra hle
    have hinter : 2 ≤ (A ∩ B).card := by omega
    obtain ⟨i, j, c, d, hij, hic, hid, hjc, hjd, hcd, hAeq, hBeq⟩ :=
      exists_shared_pair_residuals_of_three_sets hA.1 hB.1 hAB hinter
    have hBadA : SixPointBad M enum {i, j, c} := by
      rw [← hAeq]
      exact hA.2
    have hBadB : SixPointBad M enum {i, j, d} := by
      rw [← hBeq]
      exact hB.2
    exact
      (not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict enum
        hij hic hid hjc hjd hcd) ⟨hBadA, hBadB⟩

/-- The six displayed labels as a function on `Fin 6`. -/
def sixCycleMap
    (a b c d e f : Fin 6) : Fin 6 → Fin 6 :=
  ![a, b, c, d, e, f]

/-- The displayed six-label map is bijective when the labels are distinct. -/
theorem sixCycleMap_bijective
    (a b c d e f : Fin 6)
    (hSix : ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6) :
    Function.Bijective (sixCycleMap a b c d e f) := by
  obtain ⟨hab, hac, had, hae, haf,
      hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    six_pairwise_ne_of_card_six hSix
  have hinj : Function.Injective (sixCycleMap a b c d e f) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [sixCycleMap] at hxy ⊢ <;> aesop
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

/-- Six distinct displayed labels define a permutation of `Fin 6`. -/
def sixCyclePerm
    (a b c d e f : Fin 6)
    (hSix : ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6) :
    Fin 6 ≃ Fin 6 :=
  Equiv.ofBijective (sixCycleMap a b c d e f)
    (sixCycleMap_bijective a b c d e f hSix)

@[simp] theorem sixCyclePerm_apply_zero
    (a b c d e f : Fin 6) (hSix) :
    sixCyclePerm a b c d e f hSix 0 = a := by
  change sixCycleMap a b c d e f 0 = a
  rfl

@[simp] theorem sixCyclePerm_apply_one
    (a b c d e f : Fin 6) (hSix) :
    sixCyclePerm a b c d e f hSix 1 = b := by
  change sixCycleMap a b c d e f 1 = b
  rfl

@[simp] theorem sixCyclePerm_apply_two
    (a b c d e f : Fin 6) (hSix) :
    sixCyclePerm a b c d e f hSix 2 = c := by
  change sixCycleMap a b c d e f 2 = c
  rfl

@[simp] theorem sixCyclePerm_apply_three
    (a b c d e f : Fin 6) (hSix) :
    sixCyclePerm a b c d e f hSix 3 = d := by
  change sixCycleMap a b c d e f 3 = d
  rfl

@[simp] theorem sixCyclePerm_apply_four
    (a b c d e f : Fin 6) (hSix) :
    sixCyclePerm a b c d e f hSix 4 = e := by
  change sixCycleMap a b c d e f 4 = e
  rfl

@[simp] theorem sixCyclePerm_apply_five
    (a b c d e f : Fin 6) (hSix) :
    sixCyclePerm a b c d e f hSix 5 = f := by
  change sixCycleMap a b c d e f 5 = f
  rfl

/-- A three-subset outside the actual bad family is a basis. -/
theorem isBase_finSixSet_of_not_mem_badTripleFamily6
    (M : Matroid α) (enum : Fin 6 ≃ M.E)
    {T : Finset (Fin 6)}
    (hTcard : T.card = 3)
    (hTgood : T ∉ badTripleFamily6 M enum) :
    M.IsBase (finSixSet M enum T) := by
  by_contra hbad
  apply hTgood
  rw [mem_badTripleFamily6_iff]
  exact ⟨hTcard, by simpa [SixPointBad] using hbad⟩

/-- An avoiding six-cycle of position triples gives a cyclic basis order. -/
theorem cyclicBasisOrder3_of_avoidingCycle6
    (M : Matroid α) (enum : Fin 6 ≃ M.E)
    {a b c d e f : Fin 6}
    (hSix : ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6)
    (hAvoid : AvoidingCycle6 (badTripleFamily6 M enum) a b c d e f) :
    CyclicBasisOrder3 M (by omega)
      ((sixCyclePerm a b c d e f hSix).trans enum) := by
  unfold AvoidingCycle6 at hAvoid
  rcases hAvoid with ⟨h0, h1, h2, h3, h4, h5⟩
  obtain ⟨hab, hac, had, hae, haf,
      hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    six_pairwise_ne_of_card_six hSix
  have hc0 : ({a, b, c} : Finset (Fin 6)).card = 3 := by
    simp [hab, hac, hbc]
  have hc1 : ({b, c, d} : Finset (Fin 6)).card = 3 := by
    simp [hbc, hbd, hcd]
  have hc2 : ({c, d, e} : Finset (Fin 6)).card = 3 := by
    simp [hcd, hce, hde]
  have hc3 : ({d, e, f} : Finset (Fin 6)).card = 3 := by
    simp [hde, hdf, hef]
  have hc4 : ({e, f, a} : Finset (Fin 6)).card = 3 := by
    simp [hef, hae.symm, haf.symm]
  have hc5 : ({f, a, b} : Finset (Fin 6)).card = 3 := by
    simp [haf.symm, hbf.symm, hab]
  have g0 := isBase_finSixSet_of_not_mem_badTripleFamily6
    M enum hc0 h0
  have g1 := isBase_finSixSet_of_not_mem_badTripleFamily6
    M enum hc1 h1
  have g2 := isBase_finSixSet_of_not_mem_badTripleFamily6
    M enum hc2 h2
  have g3 := isBase_finSixSet_of_not_mem_badTripleFamily6
    M enum hc3 h3
  have g4 := isBase_finSixSet_of_not_mem_badTripleFamily6
    M enum hc4 h4
  have g5 := isBase_finSixSet_of_not_mem_badTripleFamily6
    M enum hc5 h5
  unfold CyclicBasisOrder3
  intro i
  fin_cases i
  · simpa [finSixSet, cyclicIndex, Set.image_insert_eq,
      Set.image_singleton] using g0
  · simpa [finSixSet, cyclicIndex, Set.image_insert_eq,
      Set.image_singleton] using g1
  · simpa [finSixSet, cyclicIndex, Set.image_insert_eq,
      Set.image_singleton] using g2
  · simpa [finSixSet, cyclicIndex, Set.image_insert_eq,
      Set.image_singleton] using g3
  · simpa [finSixSet, cyclicIndex, Set.image_insert_eq,
      Set.image_singleton] using g4
  · simpa [finSixSet, cyclicIndex, Set.image_insert_eq,
      Set.image_singleton] using g5

/--
Paper v2, Section 9: the strict six-element rank-three case, proved through
Lemma 9.2 rather than the old finite certificate.
-/
theorem exists_cyclicBasisOrder3_of_strict_two_structural
    (M : Matroid α)
    (hLoopless : M.Loopless)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = (6 : ℕ∞))
    (hStrict : StrictlyUniformlyDense M 2) :
    ∃ order : Fin 6 ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hEncard : M.E.ncard = 6 := by
    have hcast : (M.E.ncard : ℕ∞) = (6 : ℕ∞) := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast
  let : Fintype M.E := hE.fintype
  have hNatCard : Nat.card M.E = 6 := by
    simpa only [Nat.card_coe_set_eq] using hEncard
  let enum : Fin 6 ≃ M.E :=
    (Finite.equivFinOfCardEq hNatCard).symm
  have hLinear : LinearTripleFamily6 (badTripleFamily6 M enum) :=
    badTripleFamily6_linear_of_strict_two
      M hLoopless hE hRank hStrict enum
  obtain ⟨a, b, c, d, e, f, hSix, hAvoid⟩ :=
    exists_avoidingCycle6_of_linear hLinear
  refine ⟨(sixCyclePerm a b c d e f hSix).trans enum, ?_⟩
  exact cyclicBasisOrder3_of_avoidingCycle6 M enum hSix hAvoid

/-- The complete six-element uniformly dense case via the structural Section 9 proof. -/
theorem exists_cyclicBasisOrder3_of_ground_encard_six_structural
    (M : Matroid α)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = (6 : ℕ∞))
    (hDense : UniformlyDense M 2) :
    ∃ order : Fin 6 ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M 2 (by omega) hDense
  apply
    exists_cyclicBasisOrder3_of_strict_case
      M 2 (by omega) hE hRank
      (by simpa using hEcard) hDense
  intro hStrict
  simpa using
    exists_cyclicBasisOrder3_of_strict_two_structural
      M hLoopless hE hRank hEcard hStrict

#print axioms Rank3KUM.Version2.exists_cyclicBasisOrder3_of_strict_two_structural
#print axioms Rank3KUM.Version2.exists_cyclicBasisOrder3_of_ground_encard_six_structural

end

end Rank3KUM.Version2
