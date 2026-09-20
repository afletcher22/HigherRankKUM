import Rank3KUM.TwoGap.RankThreeTools

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/--
In the unequal-singleton branch, let `D = {t,r,s}`, where `t` is the unique
partner for `b` against `P = {p,a,b}`, and `t` is also a partner for `a`
against `C = {a,b,c}`. If `s` supports exchange with `b`, then the remaining
element `r` cannot support exchange with `b` as well.

Otherwise the two failed opposite exchanges against `P` put both `r` and `s`
in `cl {p,a}`. Their independent pair then spans the same line, forcing `a`
into `cl {r,s}`, contrary to the basis obtained from the partner `t`.
-/
theorem not_mem_fundamentalSupport_third_of_unequal_singleton_partners
    (M : Matroid α) {D : Set α} {p a b c t r s : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hP : M.IsBase ({p, a, b} : Set α))
    (hpD : p ∉ D) (haD : a ∉ D) (hbD : b ∉ D)
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (htr : t ≠ r) (hts : t ≠ s) (hrs : r ≠ s)
    (hDset : D = ({t, r, s} : Set α))
    (hXP :
      SymmetricPartners M D ({p, a, b} : Set α) b = {t})
    (htXC :
      t ∈ SymmetricPartners M D ({a, b, c} : Set α) a)
    (hsSupp : s ∈ FundamentalSupport M D b) :
    r ∉ FundamentalSupport M D b := by
  intro hrSupp

  have htD : t ∈ D := by
    rw [hDset]
    simp
  have hrD : r ∈ D := by
    rw [hDset]
    simp
  have hsD : s ∈ D := by
    rw [hDset]
    simp

  have hpt : p ≠ t := by
    intro h
    apply hpD
    rw [h]
    exact htD
  have hpr : p ≠ r := by
    intro h
    apply hpD
    rw [h]
    exact hrD
  have hps : p ≠ s := by
    intro h
    apply hpD
    rw [h]
    exact hsD
  have hat : a ≠ t := by
    intro h
    apply haD
    rw [h]
    exact htD
  have har : a ≠ r := by
    intro h
    apply haD
    rw [h]
    exact hrD
  have has : a ≠ s := by
    intro h
    apply haD
    rw [h]
    exact hsD
  have hbt : b ≠ t := by
    intro h
    apply hbD
    rw [h]
    exact htD
  have hbr : b ≠ r := by
    intro h
    apply hbD
    rw [h]
    exact hrD
  have hbs : b ≠ s := by
    intro h
    apply hbD
    rw [h]
    exact hsD

  have hsNotXP :
      s ∉ SymmetricPartners M D ({p, a, b} : Set α) b := by
    rw [hXP]
    simp only [Set.mem_singleton_iff]
    intro hst
    exact hts hst.symm
  have hrNotXP :
      r ∉ SymmetricPartners M D ({p, a, b} : Set α) b := by
    rw [hXP]
    simp only [Set.mem_singleton_iff]
    intro hrt
    exact htr hrt.symm

  have hsNotP : s ∉ ({p, a, b} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hps.symm, has.symm, hbs.symm⟩
  have hrNotP : r ∉ ({p, a, b} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hpr.symm, har.symm, hbr.symm⟩

  have hsOppNot :
      ¬ M.IsBase (exchangeSet ({p, a, b} : Set α) b s) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hP (by simp) hbD hsNotP hsSupp hsNotXP
  have hrOppNot :
      ¬ M.IsBase (exchangeSet ({p, a, b} : Set α) b r) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hP (by simp) hbD hrNotP hrSupp hrNotXP

  have hsTripleNot : ¬ M.IsBase ({p, a, s} : Set α) := by
    rw [exchangeSet_triple_remove_third hpb.symm hab.symm hbs.symm]
      at hsOppNot
    exact hsOppNot
  have hrTripleNot : ¬ M.IsBase ({p, a, r} : Set α) := by
    rw [exchangeSet_triple_remove_third hpb.symm hab.symm hbr.symm]
      at hrOppNot
    exact hrOppNot

  have hpaI : M.Indep ({p, a} : Set α) := by
    apply hP.indep.subset
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

  have hsE : s ∈ M.E := hD.subset_ground hsD
  have hrE : r ∈ M.E := hD.subset_ground hrD
  have hsCl : s ∈ M.closure ({p, a} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank hpaI hsE
      hpa hps has hsTripleNot
  have hrCl : r ∈ M.closure ({p, a} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank hpaI hrE
      hpa hpr har hrTripleNot

  have hrsI : M.Indep ({r, s} : Set α) := by
    apply hD.indep.subset
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hrD
    · exact hsD
  have hrsSub :
      ({r, s} : Set α) ⊆ M.closure ({p, a} : Set α) := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hrCl
    · exact hsCl
  have hDfinite : D.Finite :=
    Set.finite_of_encard_eq_coe (hD.encard_eq_eRank.trans hRank)
  have hrsFinite : ({r, s} : Set α).Finite := by
    apply hDfinite.subset
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hrD
    · exact hsD
  have hPairCard :
      ({r, s} : Set α).encard = ({p, a} : Set α).encard := by
    rw [Set.encard_pair hrs, Set.encard_pair hpa]
  have hClosure :
      M.closure ({r, s} : Set α) = M.closure ({p, a} : Set α) :=
    closure_eq_of_indep_of_subset_closure_of_encard_eq
      M hrsI hpaI hrsFinite hrsSub hPairCard

  have haClPA : a ∈ M.closure ({p, a} : Set α) :=
    M.mem_closure_of_mem (by simp) hpaI.subset_ground
  have haClRS : a ∈ M.closure ({r, s} : Set α) := by
    rw [hClosure]
    exact haClPA

  have htXC' :=
    (mem_symmetricPartners M D ({a, b, c} : Set α) a t).mp htXC
  have hDtA : M.IsBase (exchangeSet D t a) := htXC'.2.2.1
  have hExchange :
      exchangeSet D t a = ({a, r, s} : Set α) := by
    calc
      exchangeSet D t a =
          exchangeSet ({t, r, s} : Set α) t a :=
        congrArg (fun X : Set α => exchangeSet X t a) hDset
      _ = ({a, r, s} : Set α) :=
        exchangeSet_triple_remove_first htr hts hat
  have hBaseARS : M.IsBase ({a, r, s} : Set α) := by
    rw [← hExchange]
    exact hDtA
  have hSet :
      ({a, r, s} : Set α) = ({r, s, a} : Set α) := by
    ext u
    simp [or_comm, or_left_comm]
  have hBaseRSA : M.IsBase ({r, s, a} : Set α) := by
    rw [← hSet]
    exact hBaseARS
  have haNotClRS : a ∉ M.closure ({r, s} : Set α) :=
    not_mem_closure_pair_of_isBase_triple M hBaseRSA har.symm has.symm
  exact haNotClRS haClRS

end Rank3KUM.TwoGap
