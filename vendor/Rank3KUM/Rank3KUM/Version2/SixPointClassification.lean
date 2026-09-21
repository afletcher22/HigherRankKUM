import Rank3KUM.Version2.SixPointStructural

namespace Rank3KUM.Version2

open Finset

/-- The first canonical maximal configuration: two disjoint triples covering all six points. -/
def PairPattern6 (F : Finset (Finset (Fin 6))) : Prop :=
  ∃ a b c d e f : Fin 6,
    ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6 ∧
    F = {({a, b, c} : Finset (Fin 6)), ({d, e, f} : Finset (Fin 6))}

/-- Every two distinct members meet. -/
def PairwiseIntersecting6 (F : Finset (Finset (Fin 6))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ Disjoint A B

/-- Distinct members of a linear pairwise-intersecting triple family meet in exactly one point. -/
theorem card_inter_eq_one_of_pairwiseIntersecting6
    {F : Finset (Finset (Fin 6))}
    (hF : LinearTripleFamily6 F)
    (hInt : PairwiseIntersecting6 F)
    {A B : Finset (Fin 6)}
    (hAF : A ∈ F) (hBF : B ∈ F) (hAB : A ≠ B) :
    (A ∩ B).card = 1 := by
  have hle := hF.2 A hAF B hBF hAB
  have hne : (A ∩ B).Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp (hInt A hAF B hBF hAB)
  have hpos : 0 < (A ∩ B).card := Finset.card_pos.mpr hne
  omega

/-- Two disjoint members of a linear triple family force the family to consist exactly of them. -/
theorem eq_pair_of_disjoint_members
    {F : Finset (Finset (Fin 6))}
    (hF : LinearTripleFamily6 F)
    {A B : Finset (Fin 6)}
    (hAF : A ∈ F) (hBF : B ∈ F)
    (hAB : A ≠ B)
    (hdisj : Disjoint A B) :
    F = {A, B} := by
  classical
  have hAcard : A.card = 3 := hF.1 A hAF
  have hBcard : B.card = 3 := hF.1 B hBF
  have hUnionCard : (A ∪ B).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard]
  have hUnion : A ∪ B = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using hUnionCard
  apply Finset.Subset.antisymm
  · intro T hTF
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases hTA : T = A
    · exact Or.inl hTA
    by_cases hTB : T = B
    · exact Or.inr hTB
    exfalso
    have hTAle : (T ∩ A).card ≤ 1 := hF.2 T hTF A hAF hTA
    have hTBle : (T ∩ B).card ≤ 1 := hF.2 T hTF B hBF hTB
    have hsplit : T = (T ∩ A) ∪ (T ∩ B) := by
      ext x
      have hxAB : x ∈ A ∪ B := by
        rw [hUnion]
        exact Finset.mem_univ x
      rw [Finset.mem_union] at hxAB
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hxT
        rcases hxAB with hxA | hxB
        · exact Or.inl ⟨hxT, hxA⟩
        · exact Or.inr ⟨hxT, hxB⟩
      · rintro (⟨hxT, _⟩ | ⟨hxT, _⟩) <;> exact hxT
    have hTcard : T.card = 3 := hF.1 T hTF
    have hcardeq :
        T.card = ((T ∩ A) ∪ (T ∩ B)).card :=
      congrArg Finset.card hsplit
    have hcardUnion :
        ((T ∩ A) ∪ (T ∩ B)).card ≤
          (T ∩ A).card + (T ∩ B).card :=
      Finset.card_union_le (T ∩ A) (T ∩ B)
    have hcardle : T.card ≤ (T ∩ A).card + (T ∩ B).card := by
      omega
    omega
  · intro T hT
    rw [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact hAF
    · exact hBF

/-- Hence the disjoint case is, up to naming its six points, the first canonical pattern. -/
theorem pairPattern6_of_disjoint_members
    {F : Finset (Finset (Fin 6))}
    (hF : LinearTripleFamily6 F)
    {A B : Finset (Fin 6)}
    (hAF : A ∈ F) (hBF : B ∈ F)
    (hAB : A ≠ B)
    (hdisj : Disjoint A B) :
    PairPattern6 F := by
  classical
  have hAcard : A.card = 3 := hF.1 A hAF
  have hBcard : B.card = 3 := hF.1 B hBF
  obtain ⟨a, b, c, hab, hac, hbc, hA⟩ := Finset.card_eq_three.mp hAcard
  obtain ⟨d, e, f, hde, hdf, hef, hB⟩ := Finset.card_eq_three.mp hBcard
  have hUnionCard : (A ∪ B).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard]
  have hSixCard : ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6 := by
    have hEq : ({a, b, c, d, e, f} : Finset (Fin 6)) = A ∪ B := by
      rw [hA, hB]
      ext x
      simp [or_left_comm]
    rw [hEq, hUnionCard]
  refine ⟨a, b, c, d, e, f, hSixCard, ?_⟩
  rw [eq_pair_of_disjoint_members hF hAF hBF hAB hdisj, hA, hB]

end Rank3KUM.Version2
