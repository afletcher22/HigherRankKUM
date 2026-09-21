import Rank3KUM.TwoGap.Partners
import Rank3KUM.TwoGap.Closure
import Mathlib.Tactic

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/-- Delete the middle element of a displayed triple and insert a replacement. -/
theorem exchangeSet_triple_remove_second
    {x y z e : α}
    (hyx : y ≠ x) (hyz : y ≠ z) (hey : e ≠ y) :
    exchangeSet ({x, y, z} : Set α) y e =
      ({x, e, z} : Set α) := by
  ext u
  simp only [exchangeSet, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  aesop

/-- Three pairwise-distinct displayed elements have extended cardinality three. -/
theorem encard_triple_eq_three
    {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Set α).encard = 3 := by
  rw [Set.encard_insert_of_notMem]
  · rw [Set.encard_pair hyz]
    norm_num
  · simp [hxy, hxz]

/-- In rank three, a ground-set set of cardinality three is dependent if it is not a basis. -/
theorem dep_of_not_isBase_of_encard_eq_three
    (M : Matroid α) {X : Set α}
    (hRank : M.eRank = 3)
    (hXE : X ⊆ M.E)
    (hcard : X.encard = 3)
    (hnot : ¬ M.IsBase X) :
    M.Dep X := by
  refine ⟨?_, hXE⟩
  intro hI
  apply hnot
  have hfin : X.Finite := Set.finite_of_encard_eq_coe hcard
  apply hI.isBase_of_eRk_ge hfin
  exact (hRank.trans (hcard.symm.trans hI.eRk_eq_encard.symm)).le

/-- A nonbasis triple of distinct ground elements is dependent in rank three. -/
theorem dep_triple_of_not_isBase
    (M : Matroid α) {x y z : α}
    (hRank : M.eRank = 3)
    (hxE : x ∈ M.E) (hyE : y ∈ M.E) (hzE : z ∈ M.E)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hnot : ¬ M.IsBase ({x, y, z} : Set α)) :
    M.Dep ({x, y, z} : Set α) := by
  apply dep_of_not_isBase_of_encard_eq_three M hRank
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact hxE
    · exact hyE
    · exact hzE
  · exact encard_triple_eq_three hxy hxz hyz
  · exact hnot

/-- If an independent pair becomes a nonbasis triple after adjoining `z`, then `z` is in its closure. -/
theorem mem_closure_pair_of_not_isBase_triple
    (M : Matroid α) {x y z : α}
    (hRank : M.eRank = 3)
    (hxyI : M.Indep ({x, y} : Set α))
    (hzE : z ∈ M.E)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hnot : ¬ M.IsBase ({x, y, z} : Set α)) :
    z ∈ M.closure ({x, y} : Set α) := by
  have hxE : x ∈ M.E := hxyI.subset_ground (by simp)
  have hyE : y ∈ M.E := hxyI.subset_ground (by simp)
  have hdep : M.Dep ({x, y, z} : Set α) :=
    dep_triple_of_not_isBase M hRank hxE hyE hzE hxy hxz hyz hnot
  have hzxy : z ∉ ({x, y} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hzx => hxz hzx.symm, fun hzy => hyz hzy.symm⟩
  have heq :
      insert z ({x, y} : Set α) = ({x, y, z} : Set α) := by
    ext u
    simp [or_comm, or_left_comm]
  apply (hxyI.mem_closure_iff_of_notMem hzxy).2
  rwa [heq]

/-- Two finite independent sets of equal size have equal closures when one lies in the other's closure. -/
theorem closure_eq_of_indep_of_subset_closure_of_encard_eq
    (M : Matroid α) {I J : Set α}
    (hI : M.Indep I) (hJ : M.Indep J)
    (hIfin : I.Finite)
    (hIJ : I ⊆ M.closure J)
    (hcard : I.encard = J.encard) :
    M.closure I = M.closure J := by
  have hBasis : M.IsBasis I (M.closure J) := by
    apply hI.isBasis_of_eRk_ge hIfin hIJ
    exact (calc
      M.eRk (M.closure J) = M.eRk J := M.eRk_closure_eq J
      _ = J.encard := hJ.eRk_eq_encard
      _ = I.encard := hcard.symm
      _ = M.eRk I := hI.eRk_eq_encard.symm).le
  exact hBasis.closure_eq_right

/-- A support element that is not a symmetric partner must fail the opposite exchange. -/
theorem not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
    (M : Matroid α) {D B : Set α} {e d : α}
    (hD : M.IsBase D) (hB : M.IsBase B)
    (heB : e ∈ B) (heD : e ∉ D)
    (hdB : d ∉ B)
    (hdSupp : d ∈ FundamentalSupport M D e)
    (hdNot : d ∉ SymmetricPartners M D B e) :
    ¬ M.IsBase (exchangeSet B e d) := by
  intro hother
  apply hdNot
  have heE : e ∈ M.E := hB.subset_ground heB
  have hd :=
    (mem_fundamentalSupport_iff_exchange_isBase M hD heE heD).mp hdSupp
  exact (mem_symmetricPartners M D B e d).2
    ⟨hd.1, hdB, hd.2, hother⟩

/-- If the fundamental support is exactly a pair, the adjoined element lies in that pair's closure. -/
theorem mem_closure_pair_of_fundamentalSupport_eq_pair
    (M : Matroid α) {D : Set α} {e d₁ d₂ : α}
    (hD : M.IsBase D) (heE : e ∈ M.E) (heD : e ∉ D)
    (hd₁D : d₁ ∈ D) (hd₂D : d₂ ∈ D)
    (hsupp : FundamentalSupport M D e = ({d₁, d₂} : Set α)) :
    e ∈ M.closure ({d₁, d₂} : Set α) := by
  have hC : M.IsCircuit (M.fundCircuit e D) :=
    hD.fundCircuit_isCircuit heE heD
  have hFC :
      M.fundCircuit e D = ({e, d₁, d₂} : Set α) := by
    calc
      M.fundCircuit e D =
          insert e (M.fundCircuit e D \ {e}) := by
        rw [insert_sdiff_singleton,
          insert_eq_of_mem (M.mem_fundCircuit e D)]
      _ = insert e ({d₁, d₂} : Set α) := by
        change insert e (FundamentalSupport M D e) =
          insert e ({d₁, d₂} : Set α)
        rw [hsupp]
      _ = ({e, d₁, d₂} : Set α) := rfl
  rw [hFC] at hC
  have hpairI : M.Indep ({d₁, d₂} : Set α) := by
    apply hD.indep.subset
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hd₁D
    · exact hd₂D
  have hed₁ : e ≠ d₁ := by
    intro h
    apply heD
    rw [h]
    exact hd₁D
  have hed₂ : e ≠ d₂ := by
    intro h
    apply heD
    rw [h]
    exact hd₂D
  have hepair : e ∉ ({d₁, d₂} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hed₁, hed₂⟩
  exact (hpairI.mem_closure_iff_of_notMem hepair).2 hC.dep

/-- The final element of a basis triple is outside the closure of the first two. -/
theorem not_mem_closure_pair_of_isBase_triple
    (M : Matroid α) {x y z : α}
    (hB : M.IsBase ({x, y, z} : Set α))
    (hxz : x ≠ z) (hyz : y ≠ z) :
    z ∉ M.closure ({x, y} : Set α) := by
  have hpairI : M.Indep ({x, y} : Set α) := by
    apply hB.indep.subset
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hzE : z ∈ M.E := hB.subset_ground (by simp)
  have hzpair : z ∉ ({x, y} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hzx => hxz hzx.symm, fun hzy => hyz hzy.symm⟩
  apply (hpairI.notMem_closure_iff_of_notMem hzpair hzE).2
  have heq :
      insert z ({x, y} : Set α) = ({x, y, z} : Set α) := by
    ext u
    simp [or_comm, or_left_comm]
  rw [heq]
  exact hB.indep

end Rank3KUM.TwoGap
