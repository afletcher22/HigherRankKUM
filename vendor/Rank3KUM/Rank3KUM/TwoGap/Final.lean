import Rank3KUM.TwoGap.EqualContradiction

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/-- The frozen unrestricted universal two-gap insertion theorem. -/
theorem universalTwoGapInsertion
    (M : Matroid α) :
    UniversalTwoGapInsertion M := by
  unfold UniversalTwoGapInsertion
  intro hRank D p a b c q hD hdistinct hp ha hb hc hq hP hC hQ

  have hpAll := (List.pairwise_cons.mp hdistinct).1
  have htailA := (List.pairwise_cons.mp hdistinct).2
  have haAll := (List.pairwise_cons.mp htailA).1
  have htailB := (List.pairwise_cons.mp htailA).2
  have hbAll := (List.pairwise_cons.mp htailB).1
  have htailC := (List.pairwise_cons.mp htailB).2
  have hcAll := (List.pairwise_cons.mp htailC).1

  have hpa : p ≠ a := hpAll a (by simp)
  have hpb : p ≠ b := hpAll b (by simp)
  have hab : a ≠ b := haAll b (by simp)
  have hac : a ≠ c := haAll c (by simp)
  have hbc : b ≠ c := hbAll c (by simp)
  have hbq : b ≠ q := hbAll q (by simp)
  have hcq : c ≠ q := hcAll q (by simp)

  unfold TwoGapConclusion
  by_cases hFirst : FirstGapWorks M D p a b c
  · exact Or.inl hFirst
  by_cases hSecond : SecondGapWorks M D a b c q
  · exact Or.inr hSecond

  have hFirstBlocked :
      GapBlocked
        (SymmetricPartners M D ({p, a, b} : Set α) b)
        (SymmetricPartners M D ({a, b, c} : Set α) a) :=
    firstGapBlocked_of_not_works M hRank hD ha.2 hb.2
      hpb hab hab.symm hac.symm hFirst
  have hSecondBlocked :
      GapBlocked
        (SymmetricPartners M D ({a, b, c} : Set α) c)
        (SymmetricPartners M D ({b, c, q} : Set α) b) :=
    secondGapBlocked_of_not_works M hRank hD hb.2 hc.2
      hac hbc hbc.symm hbq.symm hSecond

  obtain ⟨t, hXP, hXCa⟩ :=
    (gapBlocked_symmetricPartners_iff_common_singleton
      M hD hP (by simp) hb.2 hC (by simp) ha.2).mp hFirstBlocked
  obtain ⟨s, hXCc, hXQ⟩ :=
    (gapBlocked_symmetricPartners_iff_common_singleton
      M hD hC (by simp) hc.2 hQ (by simp) hb.2).mp hSecondBlocked

  by_cases hts : t = s
  · subst s
    exact (false_of_equal_singleton_partner_pairs
      M hRank hD hP hC hQ
      hp.2 ha.2 hb.2 hc.2 hq.2
      hpa hpb hab hac hbc hbq hcq
      hXP hXCa hXCc hXQ).elim
  · exact (false_of_unequal_singleton_partner_pairs
      M hRank hD hP hC hQ
      hp.2 ha.2 hb.2 hc.2
      hpa hpb hab hac hbc
      hXP hXCa hXCc hXQ hts).elim

#print axioms Rank3KUM.TwoGap.universalTwoGapInsertion

end Rank3KUM.TwoGap
