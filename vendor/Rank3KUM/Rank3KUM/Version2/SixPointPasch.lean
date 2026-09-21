import Rank3KUM.Version2.SixPointMaximal

namespace Rank3KUM.Version2

open Finset

/-- The second canonical maximal configuration, the four triples of the Pasch pattern. -/
def PaschPattern6 (F : Finset (Finset (Fin 6))) : Prop :=
  ∃ pAB pAC pAD pBC pBD pCD : Fin 6,
    ({pAB, pAC, pAD, pBC, pBD, pCD} : Finset (Fin 6)).card = 6 ∧
    F = {
      ({pAB, pAC, pAD} : Finset (Fin 6)),
      ({pAB, pBC, pBD} : Finset (Fin 6)),
      ({pAC, pBC, pCD} : Finset (Fin 6)),
      ({pAD, pBD, pCD} : Finset (Fin 6))}

/-- A point cannot lie in three distinct members of a linear triple family on six points. -/
theorem disjoint_pair_inter_third_of_linear
    {F : Finset (Finset (Fin 6))}
    (hF : LinearTripleFamily6 F)
    {A B C : Finset (Fin 6)}
    (hAF : A ∈ F) (hBF : B ∈ F) (hCF : C ∈ F)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    Disjoint (A ∩ B) C := by
  classical
  apply Finset.disjoint_left.2
  intro x hxAB hxC
  have hxA : x ∈ A := (Finset.mem_inter.mp hxAB).1
  have hxB : x ∈ B := (Finset.mem_inter.mp hxAB).2
  have hsub : ({A, B, C} : Finset (Finset (Fin 6))) ⊆
      F.filter (fun T => x ∈ T) := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hAF, hxA⟩
    · exact Finset.mem_filter.mpr ⟨hBF, hxB⟩
    · exact Finset.mem_filter.mpr ⟨hCF, hxC⟩
  have hthree : ({A, B, C} : Finset (Finset (Fin 6))).card = 3 :=
    Finset.card_eq_three.mpr ⟨A, B, C, hAB, hAC, hBC, rfl⟩
  have hdeg_ge : 3 ≤ pointDegree6 F x := by
    unfold pointDegree6
    rw [← hthree]
    exact Finset.card_le_card hsub
  have hdeg_le := pointDegree6_le_two F hF x
  omega

/-- A point of one pair intersection differs from every point in any third family member. -/
theorem pairIntersection_point_ne_of_three_distinct
    {F : Finset (Finset (Fin 6))}
    (hF : LinearTripleFamily6 F)
    {A B C : Finset (Fin 6)}
    (hAF : A ∈ F) (hBF : B ∈ F) (hCF : C ∈ F)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    {p q : Fin 6}
    (hp : p ∈ A ∩ B) (hq : q ∈ C) :
    p ≠ q := by
  intro hpq
  subst q
  exact
    Finset.disjoint_left.mp
      (disjoint_pair_inter_third_of_linear hF hAF hBF hCF hAB hAC hBC)
      hp hq

/--
A pairwise-intersecting maximal linear triple family on six points is the
Pasch configuration, up to relabeling.  The six labels are the six pairwise
intersections of the four triples, i.e. the edges of `K₄`.
-/
theorem paschPattern6_of_maximal_pairwiseIntersecting
    {F : Finset (Finset (Fin 6))}
    (hMax : MaximalLinearTripleFamily6 F)
    (hInt : PairwiseIntersecting6 F) :
    PaschPattern6 F := by
  classical
  have hcard : F.card = 4 :=
    maximalLinearTripleFamily6_card_eq_four_of_pairwiseIntersecting hMax hInt
  obtain ⟨A, B, C, D, hAB, hAC, hAD, hBC, hBD, hCD, hFfour⟩ :=
    Finset.card_eq_four.mp hcard
  have hAF : A ∈ F := by rw [hFfour]; simp
  have hBF : B ∈ F := by rw [hFfour]; simp
  have hCF : C ∈ F := by rw [hFfour]; simp
  have hDF : D ∈ F := by rw [hFfour]; simp
  have hAcard : A.card = 3 := hMax.1.1 A hAF
  have hBcard : B.card = 3 := hMax.1.1 B hBF
  have hCcard : C.card = 3 := hMax.1.1 C hCF
  have hDcard : D.card = 3 := hMax.1.1 D hDF

  have hIAB : (A ∩ B).card = 1 :=
    card_inter_eq_one_of_pairwiseIntersecting6 hMax.1 hInt hAF hBF hAB
  have hIAC : (A ∩ C).card = 1 :=
    card_inter_eq_one_of_pairwiseIntersecting6 hMax.1 hInt hAF hCF hAC
  have hIAD : (A ∩ D).card = 1 :=
    card_inter_eq_one_of_pairwiseIntersecting6 hMax.1 hInt hAF hDF hAD
  have hIBC : (B ∩ C).card = 1 :=
    card_inter_eq_one_of_pairwiseIntersecting6 hMax.1 hInt hBF hCF hBC
  have hIBD : (B ∩ D).card = 1 :=
    card_inter_eq_one_of_pairwiseIntersecting6 hMax.1 hInt hBF hDF hBD
  have hICD : (C ∩ D).card = 1 :=
    card_inter_eq_one_of_pairwiseIntersecting6 hMax.1 hInt hCF hDF hCD

  obtain ⟨pAB, hpABset⟩ := Finset.card_eq_one.mp hIAB
  obtain ⟨pAC, hpACset⟩ := Finset.card_eq_one.mp hIAC
  obtain ⟨pAD, hpADset⟩ := Finset.card_eq_one.mp hIAD
  obtain ⟨pBC, hpBCset⟩ := Finset.card_eq_one.mp hIBC
  obtain ⟨pBD, hpBDset⟩ := Finset.card_eq_one.mp hIBD
  obtain ⟨pCD, hpCDset⟩ := Finset.card_eq_one.mp hICD

  have hpAB : pAB ∈ A ∩ B := by rw [hpABset]; simp
  have hpAC : pAC ∈ A ∩ C := by rw [hpACset]; simp
  have hpAD : pAD ∈ A ∩ D := by rw [hpADset]; simp
  have hpBC : pBC ∈ B ∩ C := by rw [hpBCset]; simp
  have hpBD : pBD ∈ B ∩ D := by rw [hpBDset]; simp
  have hpCD : pCD ∈ C ∩ D := by rw [hpCDset]; simp

  have hpAB_A := (Finset.mem_inter.mp hpAB).1
  have hpAB_B := (Finset.mem_inter.mp hpAB).2
  have hpAC_A := (Finset.mem_inter.mp hpAC).1
  have hpAC_C := (Finset.mem_inter.mp hpAC).2
  have hpAD_A := (Finset.mem_inter.mp hpAD).1
  have hpAD_D := (Finset.mem_inter.mp hpAD).2
  have hpBC_B := (Finset.mem_inter.mp hpBC).1
  have hpBC_C := (Finset.mem_inter.mp hpBC).2
  have hpBD_B := (Finset.mem_inter.mp hpBD).1
  have hpBD_D := (Finset.mem_inter.mp hpBD).2
  have hpCD_C := (Finset.mem_inter.mp hpCD).1
  have hpCD_D := (Finset.mem_inter.mp hpCD).2

  have nAB_AC : pAB ≠ pAC :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hBF hCF hAB hAC hBC hpAB hpAC_C
  have nAB_AD : pAB ≠ pAD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hBF hDF hAB hAD hBD hpAB hpAD_D
  have nAB_BC : pAB ≠ pBC :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hBF hCF hAB hAC hBC hpAB hpBC_C
  have nAB_BD : pAB ≠ pBD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hBF hDF hAB hAD hBD hpAB hpBD_D
  have nAB_CD : pAB ≠ pCD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hBF hCF hAB hAC hBC hpAB hpCD_C
  have nAC_AD : pAC ≠ pAD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hCF hDF hAC hAD hCD hpAC hpAD_D
  have nAC_BC : pAC ≠ pBC :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hCF hBF hAC hAB hBC.symm hpAC hpBC_B
  have nAC_BD : pAC ≠ pBD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hCF hBF hAC hAB hBC.symm hpAC hpBD_B
  have nAC_CD : pAC ≠ pCD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hCF hDF hAC hAD hCD hpAC hpCD_D
  have nAD_BC : pAD ≠ pBC :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hDF hBF hAD hAB hBD.symm hpAD hpBC_B
  have nAD_BD : pAD ≠ pBD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hDF hBF hAD hAB hBD.symm hpAD hpBD_B
  have nAD_CD : pAD ≠ pCD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hAF hDF hCF hAD hAC hCD.symm hpAD hpCD_C
  have nBC_BD : pBC ≠ pBD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hBF hCF hDF hBC hBD hCD hpBC hpBD_D
  have nBC_CD : pBC ≠ pCD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hBF hCF hDF hBC hBD hCD hpBC hpCD_D
  have nBD_CD : pBD ≠ pCD :=
    pairIntersection_point_ne_of_three_distinct hMax.1 hBF hDF hCF hBD hBC hCD.symm hpBD hpCD_C

  have hAeq : A = {pAB, pAC, pAD} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hpAB_A
      · exact hpAC_A
      · exact hpAD_A
    · rw [hAcard]
      simp [nAB_AC, nAB_AD, nAC_AD]
  have hBeq : B = {pAB, pBC, pBD} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hpAB_B
      · exact hpBC_B
      · exact hpBD_B
    · rw [hBcard]
      simp [nAB_BC, nAB_BD, nBC_BD]
  have hCeq : C = {pAC, pBC, pCD} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hpAC_C
      · exact hpBC_C
      · exact hpCD_C
    · rw [hCcard]
      simp [nAC_BC, nAC_CD, nBC_CD]
  have hDeq : D = {pAD, pBD, pCD} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hpAD_D
      · exact hpBD_D
      · exact hpCD_D
    · rw [hDcard]
      simp [nAD_BD, nAD_CD, nBD_CD]

  have hSixCard :
      ({pAB, pAC, pAD, pBC, pBD, pCD} : Finset (Fin 6)).card = 6 := by
    simp [nAB_AC, nAB_AD, nAB_BC, nAB_BD, nAB_CD,
      nAC_AD, nAC_BC, nAC_BD, nAC_CD,
      nAD_BC, nAD_BD, nAD_CD, nBC_BD, nBC_CD, nBD_CD]
  refine ⟨pAB, pAC, pAD, pBC, pBD, pCD, hSixCard, ?_⟩
  rw [hFfour, hAeq, hBeq, hCeq, hDeq]

end Rank3KUM.Version2
