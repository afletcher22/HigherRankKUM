import Rank3KUM.TwoGap.Unequal

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/-- In rank three, an independent pair together with a ground element outside its closure is a basis. -/
theorem isBase_triple_of_indep_pair_notMem_closure_rank3
    (M : Matroid α) {x y z : α}
    (hRank : M.eRank = 3)
    (hxyI : M.Indep ({x, y} : Set α))
    (hzE : z ∈ M.E)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hz : z ∉ M.closure ({x, y} : Set α)) :
    M.IsBase ({x, y, z} : Set α) := by
  have hzPair : z ∉ ({x, y} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hxz h.symm, fun h => hyz h.symm⟩
  have hInsert : M.Indep (insert z ({x, y} : Set α)) :=
    (hxyI.notMem_closure_iff_of_notMem hzPair hzE).mp hz
  have hSet :
      insert z ({x, y} : Set α) = ({x, y, z} : Set α) := by
    ext u
    simp [or_comm, or_left_comm]
  have hTripleI : M.Indep ({x, y, z} : Set α) := by
    rwa [hSet] at hInsert
  by_contra hnot
  have hxE : x ∈ M.E := hxyI.subset_ground (by simp)
  have hyE : y ∈ M.E := hxyI.subset_ground (by simp)
  exact (dep_triple_of_not_isBase M hRank hxE hyE hzE
    hxy hxz hyz hnot).not_indep hTripleI

/--
The unequal common-singleton configuration for the two neighboring gaps is
impossible. This is the full `t ≠ s` branch of the universal two-gap proof.
-/
theorem false_of_unequal_singleton_partner_pairs
    (M : Matroid α) {D : Set α} {p a b c q t s : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hP : M.IsBase ({p, a, b} : Set α))
    (hC : M.IsBase ({a, b, c} : Set α))
    (hQ : M.IsBase ({b, c, q} : Set α))
    (hpD : p ∉ D) (haD : a ∉ D) (hbD : b ∉ D) (hcD : c ∉ D)
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hXP :
      SymmetricPartners M D ({p, a, b} : Set α) b = {t})
    (hXCa :
      SymmetricPartners M D ({a, b, c} : Set α) a = {t})
    (hXCc :
      SymmetricPartners M D ({a, b, c} : Set α) c = {s})
    (hXQ :
      SymmetricPartners M D ({b, c, q} : Set α) b = {s})
    (hts : t ≠ s) :
    False := by
  have htXP :
      t ∈ SymmetricPartners M D ({p, a, b} : Set α) b := by
    rw [hXP]
    simp
  have htXCa :
      t ∈ SymmetricPartners M D ({a, b, c} : Set α) a := by
    rw [hXCa]
    simp
  have hsXCc :
      s ∈ SymmetricPartners M D ({a, b, c} : Set α) c := by
    rw [hXCc]
    simp
  have hsXQ :
      s ∈ SymmetricPartners M D ({b, c, q} : Set α) b := by
    rw [hXQ]
    simp

  have htXP' :=
    (mem_symmetricPartners M D ({p, a, b} : Set α) b t).mp htXP
  have hsXQ' :=
    (mem_symmetricPartners M D ({b, c, q} : Set α) b s).mp hsXQ
  have htD : t ∈ D := htXP'.1
  have hsD : s ∈ D := hsXQ'.1

  have hcard : D.encard = 3 := hD.encard_eq_eRank.trans hRank
  obtain ⟨d, hd0, hd2⟩ :=
    exists_fin3_equiv_with_endpoints hcard htD hsD hts
  let r : α := (d 1 : α)
  have hDset0 := set_eq_triple_of_fin3_equiv d
  have hDset : D = ({t, r, s} : Set α) := by
    simpa [r, hd0, hd2] using hDset0
  have hrD : r ∈ D := by
    rw [hDset]
    simp
  have htr : t ≠ r := by
    have hne := fin3_equiv_coe_ne d (by omega : (0 : Fin 3) ≠ 1)
    simpa [r, hd0] using hne
  have hrs : r ≠ s := by
    have hne := fin3_equiv_coe_ne d (by omega : (1 : Fin 3) ≠ 2)
    simpa [r, hd2] using hne

  have hbE : b ∈ M.E := hP.subset_ground (by simp)
  have haE : a ∈ M.E := hC.subset_ground (by simp)
  have hcE : c ∈ M.E := hC.subset_ground (by simp)
  have hrE : r ∈ M.E := hD.subset_ground hrD

  have htSupp : t ∈ FundamentalSupport M D b :=
    symmetricPartners_subset_fundamentalSupport M hD hP
      (by simp) hbD htXP
  have hsSupp : s ∈ FundamentalSupport M D b :=
    symmetricPartners_subset_fundamentalSupport M hD hQ
      (by simp) hbD hsXQ
  have hrNotSupp : r ∉ FundamentalSupport M D b :=
    not_mem_fundamentalSupport_third_of_unequal_singleton_partners
      M hRank hD hP hpD haD hbD hpa hpb hab
      htr hts hrs hDset hXP htXCa hsSupp

  have hSuppEq :
      FundamentalSupport M D b = ({t, s} : Set α) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxD :=
        ((mem_fundamentalSupport_iff_exchange_isBase M hD hbE hbD).mp hx).1
      rw [hDset] at hxD
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxD ⊢
      rcases hxD with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact (hrNotSupp hx).elim
      · exact Or.inr rfl
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact htSupp
      · exact hsSupp

  have hbClTS : b ∈ M.closure ({t, s} : Set α) :=
    mem_closure_pair_of_fundamentalSupport_eq_pair
      M hD hbE hbD htD hsD hSuppEq

  have htXCa' :=
    (mem_symmetricPartners M D ({a, b, c} : Set α) a t).mp htXCa
  have hsXCc' :=
    (mem_symmetricPartners M D ({a, b, c} : Set α) c s).mp hsXCc

  have hta : t ≠ a := by
    intro h
    apply haD
    rw [← h]
    exact htD
  have htc : t ≠ c := by
    intro h
    apply hcD
    rw [← h]
    exact htD
  have hsb : s ≠ b := by
    intro h
    apply hbD
    rw [← h]
    exact hsD
  have hsa : s ≠ a := by
    intro h
    apply haD
    rw [← h]
    exact hsD
  have hsc : s ≠ c := by
    intro h
    apply hcD
    rw [← h]
    exact hsD
  have hra : r ≠ a := by
    intro h
    apply haD
    rw [← h]
    exact hrD
  have hrb : r ≠ b := by
    intro h
    apply hbD
    rw [← h]
    exact hrD
  have hrc : r ≠ c := by
    intro h
    apply hcD
    rw [← h]
    exact hrD

  have hBaseTBC : M.IsBase ({t, b, c} : Set α) := by
    rw [← exchangeSet_triple_remove_first hab hac hta]
    exact htXCa'.2.2.2
  have hBaseABS : M.IsBase ({a, b, s} : Set α) := by
    rw [← exchangeSet_triple_remove_third hac.symm hbc.symm hsc]
    exact hsXCc'.2.2.2

  have htsI : M.Indep ({t, s} : Set α) := by
    apply hD.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact htD
    · exact hsD

  have htb : t ≠ b := by
    intro h
    exact hbD (h ▸ htD)
  have htbI : M.Indep ({t, b} : Set α) := by
    apply hBaseTBC.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have htbSub :
      ({t, b} : Set α) ⊆ M.closure ({t, s} : Set α) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact M.mem_closure_of_mem (by simp) htsI.subset_ground
    · exact hbClTS
  have htbFinite : ({t, b} : Set α).Finite :=
    Set.finite_of_encard_eq_coe (Set.encard_pair htb)
  have htbCard :
      ({t, b} : Set α).encard = ({t, s} : Set α).encard := by
    rw [Set.encard_pair htb, Set.encard_pair hts]
  have hClosureTB :
      M.closure ({t, b} : Set α) = M.closure ({t, s} : Set α) :=
    closure_eq_of_indep_of_subset_closure_of_encard_eq
      M htbI htsI htbFinite htbSub htbCard
  have hcNotClTB : c ∉ M.closure ({t, b} : Set α) :=
    not_mem_closure_pair_of_isBase_triple M hBaseTBC htc hbc
  have hcNotClTS : c ∉ M.closure ({t, s} : Set α) := by
    rw [← hClosureTB]
    exact hcNotClTB

  have hbs : b ≠ s := hsb.symm
  have hbsI : M.Indep ({b, s} : Set α) := by
    apply hBaseABS.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hbsSub :
      ({b, s} : Set α) ⊆ M.closure ({t, s} : Set α) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hbClTS
    · exact M.mem_closure_of_mem (by simp) htsI.subset_ground
  have hbsFinite : ({b, s} : Set α).Finite :=
    Set.finite_of_encard_eq_coe (Set.encard_pair hbs)
  have hbsCard :
      ({b, s} : Set α).encard = ({t, s} : Set α).encard := by
    rw [Set.encard_pair hbs, Set.encard_pair hts]
  have hClosureBS :
      M.closure ({b, s} : Set α) = M.closure ({t, s} : Set α) :=
    closure_eq_of_indep_of_subset_closure_of_encard_eq
      M hbsI htsI hbsFinite hbsSub hbsCard
  have hSetBSA :
      ({a, b, s} : Set α) = ({b, s, a} : Set α) := by
    ext x
    simp [or_comm, or_left_comm]
  have hBaseBSA : M.IsBase ({b, s, a} : Set α) := by
    rw [← hSetBSA]
    exact hBaseABS
  have haNotClBS : a ∉ M.closure ({b, s} : Set α) :=
    not_mem_closure_pair_of_isBase_triple M hBaseBSA hab.symm hsa
  have haNotClTS : a ∉ M.closure ({t, s} : Set α) := by
    rw [← hClosureBS]
    exact haNotClBS

  have hBaseTSA : M.IsBase ({t, s, a} : Set α) :=
    isBase_triple_of_indep_pair_notMem_closure_rank3
      M hRank htsI haE hts hta hsa haNotClTS
  have hBaseTSC : M.IsBase ({t, s, c} : Set α) :=
    isBase_triple_of_indep_pair_notMem_closure_rank3
      M hRank htsI hcE hts htc hsc hcNotClTS

  have hExchangeA :
      exchangeSet D r a = ({t, a, s} : Set α) := by
    calc
      exchangeSet D r a =
          exchangeSet ({t, r, s} : Set α) r a :=
        congrArg (fun X : Set α => exchangeSet X r a) hDset
      _ = ({t, a, s} : Set α) :=
        exchangeSet_triple_remove_second htr.symm hrs hra.symm
  have hSetTSA :
      ({t, s, a} : Set α) = ({t, a, s} : Set α) := by
    ext x
    simp [or_comm, or_left_comm]
  have hExchangeABase : M.IsBase (exchangeSet D r a) := by
    rw [hExchangeA, ← hSetTSA]
    exact hBaseTSA
  have hrSuppA : r ∈ FundamentalSupport M D a :=
    (mem_fundamentalSupport_iff_exchange_isBase M hD haE haD).2
      ⟨hrD, hExchangeABase⟩

  have hExchangeC :
      exchangeSet D r c = ({t, c, s} : Set α) := by
    calc
      exchangeSet D r c =
          exchangeSet ({t, r, s} : Set α) r c :=
        congrArg (fun X : Set α => exchangeSet X r c) hDset
      _ = ({t, c, s} : Set α) :=
        exchangeSet_triple_remove_second htr.symm hrs hrc.symm
  have hSetTSC :
      ({t, s, c} : Set α) = ({t, c, s} : Set α) := by
    ext x
    simp [or_comm, or_left_comm]
  have hExchangeCBase : M.IsBase (exchangeSet D r c) := by
    rw [hExchangeC, ← hSetTSC]
    exact hBaseTSC
  have hrSuppC : r ∈ FundamentalSupport M D c :=
    (mem_fundamentalSupport_iff_exchange_isBase M hD hcE hcD).2
      ⟨hrD, hExchangeCBase⟩

  have hrNotXCa :
      r ∉ SymmetricPartners M D ({a, b, c} : Set α) a := by
    rw [hXCa]
    simp only [Set.mem_singleton_iff]
    intro hrt
    exact htr hrt.symm
  have hrNotXCc :
      r ∉ SymmetricPartners M D ({a, b, c} : Set α) c := by
    rw [hXCc]
    simp only [Set.mem_singleton_iff]
    exact hrs
  have hrNotC : r ∉ ({a, b, c} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hra, hrb, hrc⟩

  have hrOppANot :
      ¬ M.IsBase (exchangeSet ({a, b, c} : Set α) a r) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hC (by simp) haD hrNotC hrSuppA hrNotXCa
  have hrOppCNot :
      ¬ M.IsBase (exchangeSet ({a, b, c} : Set α) c r) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hC (by simp) hcD hrNotC hrSuppC hrNotXCc

  have hRBCNot : ¬ M.IsBase ({r, b, c} : Set α) := by
    rw [exchangeSet_triple_remove_first hab hac hra] at hrOppANot
    exact hrOppANot
  have hABRNot : ¬ M.IsBase ({a, b, r} : Set α) := by
    rw [exchangeSet_triple_remove_third hac.symm hbc.symm hrc] at hrOppCNot
    exact hrOppCNot
  have hSetRBC :
      ({r, b, c} : Set α) = ({b, c, r} : Set α) := by
    ext x
    simp [or_comm, or_assoc]
  have hBCRNot : ¬ M.IsBase ({b, c, r} : Set α) := by
    intro hbase
    apply hRBCNot
    rw [hSetRBC]
    exact hbase

  have hbcI : M.Indep ({b, c} : Set α) := by
    apply hC.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have habI : M.Indep ({a, b} : Set α) := by
    apply hC.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hrClBC : r ∈ M.closure ({b, c} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank hbcI hrE
      hbc hrb.symm hrc.symm hBCRNot
  have hrClAB : r ∈ M.closure ({a, b} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank habI hrE
      hab hra.symm hrb.symm hABRNot
  have hrClB : r ∈ M.closure ({b} : Set α) := by
    rw [← closure_pair_inter_closure_pair_eq M hRank hC]
    exact ⟨hrClAB, hrClBC⟩
  have hSingletonB : ({b} : Set α) ⊆ M.closure ({t, s} : Set α) := by
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ hbClTS
  have hClosureBSub :
      M.closure ({b} : Set α) ⊆ M.closure ({t, s} : Set α) :=
    M.closure_subset_closure_of_subset_closure hSingletonB
  have hrClTS : r ∈ M.closure ({t, s} : Set α) :=
    hClosureBSub hrClB

  have hDWithoutR : D \ {r} = ({t, s} : Set α) := by
    calc
      D \ {r} = ({t, r, s} : Set α) \ {r} :=
        congrArg (fun X : Set α => X \ {r}) hDset
      _ = ({t, s} : Set α) := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨hx, hxr⟩
          rcases hx with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact (hxr rfl).elim
          · exact Or.inr rfl
        · intro hx
          rcases hx with rfl | rfl
          · exact ⟨Or.inl rfl, htr⟩
          · exact ⟨Or.inr (Or.inr rfl), hrs.symm⟩
  have hrNotCl : r ∉ M.closure (D \ {r}) :=
    hD.indep.notMem_closure_sdiff_of_mem hrD
  rw [hDWithoutR] at hrNotCl
  exact hrNotCl hrClTS

end Rank3KUM.TwoGap
