import Rank3KUM.Version2.SixPointClassification

namespace Rank3KUM.Version2

open Finset

/-- A maximal linear triple family on six points is nonempty. -/
theorem maximalLinearTripleFamily6_card_ne_zero
    {F : Finset (Finset (Fin 6))}
    (hMax : MaximalLinearTripleFamily6 F) :
    F.card ≠ 0 := by
  classical
  intro hcard
  have hFempty : F = ∅ := Finset.card_eq_zero.mp hcard
  let T : Finset (Fin 6) := {0, 1, 2}
  have hTcard : T.card = 3 := by decide
  have hcompat : ∀ A ∈ F, (T ∩ A).card ≤ 1 := by
    intro A hAF
    rw [hFempty] at hAF
    simp at hAF
  have hlin : LinearTripleFamily6 (insert T F) :=
    linearTripleFamily6_insert hMax.1 hTcard hcompat
  have hmem := hMax.2 T hTcard hlin
  rw [hFempty] at hmem
  simp at hmem

/-- A maximal linear triple family on six points cannot have one member. -/
theorem maximalLinearTripleFamily6_card_ne_one
    {F : Finset (Finset (Fin 6))}
    (hMax : MaximalLinearTripleFamily6 F) :
    F.card ≠ 1 := by
  classical
  intro hcard
  obtain ⟨A, hFone⟩ := Finset.card_eq_one.mp hcard
  have hAF : A ∈ F := by rw [hFone]; simp
  have hAcard : A.card = 3 := hMax.1.1 A hAF
  let T : Finset (Fin 6) := Finset.univ \ A
  have hTcard : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), hAcard]
    norm_num
  have hcompat : ∀ B ∈ F, (T ∩ B).card ≤ 1 := by
    intro B hBF
    rw [hFone] at hBF
    simp only [Finset.mem_singleton] at hBF
    subst B
    dsimp [T]
    simp
  have hlin : LinearTripleFamily6 (insert T F) :=
    linearTripleFamily6_insert hMax.1 hTcard hcompat
  have hmem := hMax.2 T hTcard hlin
  rw [hFone] at hmem
  simp only [Finset.mem_singleton] at hmem
  have hAnon : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hxA⟩ := hAnon
  have hxT : x ∈ T := by rw [hmem]; exact hxA
  exact (Finset.mem_sdiff.mp hxT).2 hxA

/-- In the pairwise-intersecting branch, a maximal family cannot have exactly two members. -/
theorem maximalLinearTripleFamily6_card_ne_two_of_pairwiseIntersecting
    {F : Finset (Finset (Fin 6))}
    (hMax : MaximalLinearTripleFamily6 F)
    (hInt : PairwiseIntersecting6 F) :
    F.card ≠ 2 := by
  classical
  intro hcard
  obtain ⟨A, B, hAB, hFpair⟩ := Finset.card_eq_two.mp hcard
  have hAF : A ∈ F := by rw [hFpair]; simp
  have hBF : B ∈ F := by rw [hFpair]; simp
  have hAcard : A.card = 3 := hMax.1.1 A hAF
  have hBcard : B.card = 3 := hMax.1.1 B hBF
  have hIcard : (A ∩ B).card = 1 :=
    card_inter_eq_one_of_pairwiseIntersecting6 hMax.1 hInt hAF hBF hAB
  have hXACard : (A \ B).card = 2 := by
    have h := Finset.card_sdiff_add_card_inter A B
    rw [hIcard, hAcard] at h
    omega
  have hXBCard : (B \ A).card = 2 := by
    have h := Finset.card_sdiff_add_card_inter B A
    have hIcard' : (B ∩ A).card = 1 := by simpa [Finset.inter_comm] using hIcard
    rw [hIcard', hBcard] at h
    omega
  have hUnionCard : (A ∪ B).card = 5 := by
    have h := Finset.card_union_add_card_inter A B
    rw [hIcard, hAcard, hBcard] at h
    omega
  have hOCard : (Finset.univ \ (A ∪ B)).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ (A ∪ B)), hUnionCard]
    norm_num

  have hXAnon : (A \ B).Nonempty := Finset.card_pos.mp (by omega)
  have hXBnon : (B \ A).Nonempty := Finset.card_pos.mp (by omega)
  have hOnon : (Finset.univ \ (A ∪ B)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hXAnon
  obtain ⟨b, hb⟩ := hXBnon
  obtain ⟨c, hc⟩ := hOnon
  have haA : a ∈ A := (Finset.mem_sdiff.mp ha).1
  have haB : a ∉ B := (Finset.mem_sdiff.mp ha).2
  have hbB : b ∈ B := (Finset.mem_sdiff.mp hb).1
  have hbA : b ∉ A := (Finset.mem_sdiff.mp hb).2
  have hcAB : c ∉ A ∪ B := (Finset.mem_sdiff.mp hc).2
  have hcA : c ∉ A := fun hcA => hcAB (Finset.mem_union_left B hcA)
  have hcB : c ∉ B := fun hcB => hcAB (Finset.mem_union_right A hcB)
  have hab : a ≠ b := by
    intro h
    subst b
    exact haB hbB
  have hac : a ≠ c := by
    intro h
    subst c
    exact hcA haA
  have hbc : b ≠ c := by
    intro h
    subst c
    exact hcB hbB

  let T : Finset (Fin 6) := {a, b, c}
  have hTcard : T.card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hTA : T ∩ A = {a} := by
    ext x
    simp [T, haA, hbA, hcA]
  have hTB : T ∩ B = {b} := by
    ext x
    simp [T, haB, hbB, hcB]
  have hcompat : ∀ X ∈ F, (T ∩ X).card ≤ 1 := by
    intro X hXF
    rw [hFpair] at hXF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXF
    rcases hXF with rfl | rfl
    · rw [hTA]; simp
    · rw [hTB]; simp
  have hlin : LinearTripleFamily6 (insert T F) :=
    linearTripleFamily6_insert hMax.1 hTcard hcompat
  have hmem := hMax.2 T hTcard hlin
  rw [hFpair] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hcT : c ∈ T := by simp [T]
  rcases hmem with hTAeq | hTBeq
  · rw [hTAeq] at hcT
    exact hcA hcT
  · rw [hTBeq] at hcT
    exact hcB hcT

/-- In the pairwise-intersecting branch, a maximal family cannot have exactly three members. -/
theorem maximalLinearTripleFamily6_card_ne_three_of_pairwiseIntersecting
    {F : Finset (Finset (Fin 6))}
    (hMax : MaximalLinearTripleFamily6 F)
    (hInt : PairwiseIntersecting6 F) :
    F.card ≠ 3 := by
  classical
  intro hcard
  obtain ⟨A, B, C, hAB, hAC, hBC, hFthree⟩ := Finset.card_eq_three.mp hcard
  have hAF : A ∈ F := by rw [hFthree]; simp
  have hBF : B ∈ F := by rw [hFthree]; simp
  have hCF : C ∈ F := by rw [hFthree]; simp
  have hAcard : A.card = 3 := hMax.1.1 A hAF
  have hBcard : B.card = 3 := hMax.1.1 B hBF
  have hCcard : C.card = 3 := hMax.1.1 C hCF
  have hIAB : (A ∩ B).card = 1 :=
    card_inter_eq_one_of_pairwiseIntersecting6 hMax.1 hInt hAF hBF hAB
  have hIAC : (A ∩ C).card = 1 :=
    card_inter_eq_one_of_pairwiseIntersecting6 hMax.1 hInt hAF hCF hAC
  have hIBC : (B ∩ C).card = 1 :=
    card_inter_eq_one_of_pairwiseIntersecting6 hMax.1 hInt hBF hCF hBC

  have hNoTriple (x : Fin 6) (hxA : x ∈ A) (hxB : x ∈ B) (hxC : x ∈ C) : False := by
    have hsub : ({A, B, C} : Finset (Finset (Fin 6))) ⊆
        F.filter (fun T => x ∈ T) := by
      intro X hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hAF, hxA⟩
      · exact Finset.mem_filter.mpr ⟨hBF, hxB⟩
      · exact Finset.mem_filter.mpr ⟨hCF, hxC⟩
    have hthree : ({A, B, C} : Finset (Finset (Fin 6))).card = 3 :=
      Finset.card_eq_three.mpr ⟨A, B, C, hAB, hAC, hBC, rfl⟩
    have hdeg_ge : 3 ≤ pointDegree6 F x := by
      unfold pointDegree6
      rw [← hthree]
      exact Finset.card_le_card hsub
    have hdeg_le := pointDegree6_le_two F hMax.1 x
    omega

  have hABAC : Disjoint (A ∩ B) (A ∩ C) := by
    apply Finset.disjoint_left.2
    intro x hxAB hxAC
    rw [Finset.mem_inter] at hxAB hxAC
    exact hNoTriple x hxAB.1 hxAB.2 hxAC.2
  have hABBC : Disjoint (A ∩ B) (B ∩ C) := by
    apply Finset.disjoint_left.2
    intro x hxAB hxBC
    rw [Finset.mem_inter] at hxAB hxBC
    exact hNoTriple x hxAB.1 hxAB.2 hxBC.2
  have hACBC : Disjoint (A ∩ C) (B ∩ C) := by
    apply Finset.disjoint_left.2
    intro x hxAC hxBC
    rw [Finset.mem_inter] at hxAC hxBC
    exact hNoTriple x hxAC.1 hxBC.1 hxAC.2
  have hPairBC : Disjoint ((A ∩ B) ∪ (A ∩ C)) (B ∩ C) := by
    apply Finset.disjoint_left.2
    intro x hx hxBC
    rw [Finset.mem_union] at hx
    rcases hx with hxAB | hxAC
    · exact Finset.disjoint_left.mp hABBC hxAB hxBC
    · exact Finset.disjoint_left.mp hACBC hxAC hxBC

  let P : Finset (Fin 6) := ((A ∩ B) ∪ (A ∩ C)) ∪ (B ∩ C)
  have hPcard : P.card = 3 := by
    dsimp [P]
    rw [Finset.card_union_of_disjoint hPairBC,
      Finset.card_union_of_disjoint hABAC, hIAB, hIAC, hIBC]
  let T : Finset (Fin 6) := Finset.univ \ P
  have hTcard : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ P), hPcard]
    norm_num

  have hAP : A ∩ P = (A ∩ B) ∪ (A ∩ C) := by
    ext x
    simp only [P, Finset.mem_inter, Finset.mem_union]
    tauto
  have hBP : B ∩ P = (A ∩ B) ∪ (B ∩ C) := by
    ext x
    simp only [P, Finset.mem_inter, Finset.mem_union]
    tauto
  have hCP : C ∩ P = (A ∩ C) ∪ (B ∩ C) := by
    ext x
    simp only [P, Finset.mem_inter, Finset.mem_union]
    tauto
  have hAPcard : (A ∩ P).card = 2 := by
    rw [hAP, Finset.card_union_of_disjoint hABAC, hIAB, hIAC]
  have hBPcard : (B ∩ P).card = 2 := by
    rw [hBP, Finset.card_union_of_disjoint hABBC, hIAB, hIBC]
  have hCPcard : (C ∩ P).card = 2 := by
    rw [hCP, Finset.card_union_of_disjoint hACBC, hIAC, hIBC]
  have hTAeq : T ∩ A = A \ P := by
    ext x
    simp [T, and_comm]
  have hTBeq : T ∩ B = B \ P := by
    ext x
    simp [T, and_comm]
  have hTCeq : T ∩ C = C \ P := by
    ext x
    simp [T, and_comm]
  have hTAcard : (T ∩ A).card = 1 := by
    rw [hTAeq]
    have h := Finset.card_sdiff_add_card_inter A P
    rw [hAPcard, hAcard] at h
    omega
  have hTBcard : (T ∩ B).card = 1 := by
    rw [hTBeq]
    have h := Finset.card_sdiff_add_card_inter B P
    rw [hBPcard, hBcard] at h
    omega
  have hTCcard : (T ∩ C).card = 1 := by
    rw [hTCeq]
    have h := Finset.card_sdiff_add_card_inter C P
    rw [hCPcard, hCcard] at h
    omega
  have hcompat : ∀ X ∈ F, (T ∩ X).card ≤ 1 := by
    intro X hXF
    rw [hFthree] at hXF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXF
    rcases hXF with rfl | rfl | rfl
    · omega
    · omega
    · omega
  have hlin : LinearTripleFamily6 (insert T F) :=
    linearTripleFamily6_insert hMax.1 hTcard hcompat
  have hmem := hMax.2 T hTcard hlin
  rw [hFthree] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hTA | hTB | hTC
  · rw [hTA, Finset.inter_self, hAcard] at hTAcard
    omega
  · rw [hTB, Finset.inter_self, hBcard] at hTBcard
    omega
  · rw [hTC, Finset.inter_self, hCcard] at hTCcard
    omega

/-- Therefore the pairwise-intersecting maximal configuration has exactly four triples. -/
theorem maximalLinearTripleFamily6_card_eq_four_of_pairwiseIntersecting
    {F : Finset (Finset (Fin 6))}
    (hMax : MaximalLinearTripleFamily6 F)
    (hInt : PairwiseIntersecting6 F) :
    F.card = 4 := by
  have hle : F.card ≤ 4 := card_linearTripleFamily6_le_four F hMax.1
  have h0 := maximalLinearTripleFamily6_card_ne_zero hMax
  have h1 := maximalLinearTripleFamily6_card_ne_one hMax
  have h2 := maximalLinearTripleFamily6_card_ne_two_of_pairwiseIntersecting hMax hInt
  have h3 := maximalLinearTripleFamily6_card_ne_three_of_pairwiseIntersecting hMax hInt
  omega

end Rank3KUM.Version2
